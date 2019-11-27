
#[derive(Debug, PartialEq, Eq)]
pub struct CommandList(pub Vec<Command>);

#[derive(Debug, PartialEq, Eq)]
pub struct Command {
    pub table: String,
    pub action: CommandAction,
}

#[derive(Debug, PartialEq, Eq)]
pub enum CommandAction {
    RemoveColumn{col: String}
}
