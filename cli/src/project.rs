#![allow(dead_code)]
use migrate::{migrate, DbConf};
use static_checker;
use std::env::current_dir;
use std::fs::{create_dir, read_dir, read_to_string, write, File};
use std::io;
use std::path::{Path, PathBuf};

use chrono::prelude::*;

#[derive(Debug)]
pub struct Project {
    root_dir: PathBuf,
}

impl Project {
    pub fn find_from_cwd() -> io::Result<Project> {
        let mut dir = current_dir()?;
        while !contains_policy_txt(&dir)? {
            if !dir.pop() {
                return Err(io::Error::new(io::ErrorKind::NotFound, "Could not find a Cargo.toml in your current file hierarchy. Make sure to run init from within the project"));
            }
        }
        return Ok(Project { root_dir: dir });
    }

    pub fn create_migration(&self, name: &str) -> io::Result<PathBuf> {
        let dt = Utc::now();
        let timestamp = dt.format("%Y%m%d%H%M%S");
        let fname = format!("{}-{}", timestamp, name);
        let new_dir = self.migration_dir().join(fname);

        create_dir(new_dir.clone())?;
        File::create(new_dir.join("up.mig"))?;
        Ok(new_dir)
    }

    pub fn migrations(&self) -> io::Result<impl Iterator<Item = Migration>> {
        let iter = read_dir(self.migration_dir())?
            .filter_map(|m| m.ok())
            .map(|m_file| Migration::from_path(m_file.path()));

        Ok(iter)
    }

    pub fn dry_run_migration(&self, file_path: impl AsRef<Path>) -> Result<String, String> {
        static_checker::migrate::migrate_policy_from_files(self.policy_file(), file_path)
            .map_err(|e| e.to_string())
    }

    pub fn run_migration(&self, file_path: impl AsRef<Path>) -> Result<(), String> {
        fn stringify(err: io::Error) -> String {
            format!("{}", err)
        }
        let fp_ref = file_path.as_ref();
        let policy = read_to_string(self.policy_file()).map_err(stringify)?;
        let migration = read_to_string(fp_ref).map_err(stringify)?;
        let migration_name = fp_ref
            .file_stem()
            .expect("Cannot extract filename")
            .to_str()
            .expect("Not a valid string");
        // It's important that we try to generate the new policy first, in case the migration is invalid
        let new_policy = self.dry_run_migration(fp_ref)?;
        // Then do the actual data migration
        migrate(
            self.db_conf().map_err(stringify)?,
            &policy,
            &migration,
            &migration_name,
        )?;

        // Finally, write the new policy to disk
        write(self.policy_file(), new_policy).map_err(stringify)?;

        Ok(())
    }

    pub fn policy_file(&self) -> PathBuf {
        self.root_dir.join("policy.txt")
    }

    fn db_conf(&self) -> io::Result<DbConf> {
        let conf: toml::Value = toml::from_str(&read_to_string(self.root_dir.join("db.toml"))?)?;
        Ok(DbConf {
            host: conf["host"].as_str().unwrap().to_string(),
            port: conf["port"].as_integer().unwrap() as u16,
            db_name: conf["db"].as_str().unwrap().to_string(),
        })
    }

    fn migration_dir(&self) -> PathBuf {
        self.root_dir.join("migrations")
    }
}

const DATE_LEN: usize = 4;
const MONTH_LEN: usize = 2;
const DAY_LEN: usize = 2;
const TIME_LEN: usize = 6;

#[derive(Debug)]
pub struct Migration {
    path: PathBuf,
}

impl Migration {
    fn from_path(path: PathBuf) -> Self {
        Self { path }
    }

    pub fn timestamp(&self) -> Timestamp {
        let fname = self
            .path
            .file_name()
            .expect("All migration files should have names");
        let date_str = &fname.to_string_lossy()[..(DATE_LEN + MONTH_LEN + DAY_LEN + TIME_LEN)];
        Timestamp(
            date_str
                .parse()
                .expect("Migration file names should start with timestamps"),
        )
    }
}

#[derive(Debug, PartialOrd, Ord, PartialEq, Eq)]
pub struct Timestamp(u64);

fn contains_policy_txt(dir: &PathBuf) -> io::Result<bool> {
    for entry in read_dir(dir)? {
        let entry = entry?;
        if entry.file_name() == "policy.txt" {
            return Ok(true);
        }
    }
    return Ok(false);
}
