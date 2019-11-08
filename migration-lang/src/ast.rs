
#[derive(Debug, PartialEq, Eq)]
pub struct CommandList(pub Vec<Command>);

#[derive(Debug, PartialEq, Eq)]
pub enum Command {
    RemoveColumn{table: String, col: String}
}
