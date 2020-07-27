# Safe Policy Migrations

## Repository Map

- [`cli`] - Implements the `migrate` command that's used for executing migrations

- [`mongodb-enforcement`] - Contains the runtime enforcement (including codegen) for enforcing policies during program execution

- [`mongodb-migrate`] - Contains the logic to perform migrations against a mongodb database ([`cli`] relies on this)gi

- [`static-checker`] - Implements SMT-based checking of policies and policy functions to ensure that new policies are stricter than old policies.

- [`policy-lang`] - Implements parser, name resolution, and type-checker for the policy language (including migration).

[`cli`]: ./cli
[`mongodb-enforcement`]: ./mongodb-enforcement
[`mongodb-migrate`]: ./mongodb-migrate
[`static-checker`]: ./static-checker
[`policy-lang`]: ./policy-lang
