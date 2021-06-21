![Scooter: A DSL for policy-aware-migrations](./web-demo/static/img/scooter-copy.svg)

This repository contains the source code for Scooter, Sidecar, and several case studies as described in **Scooter & Sidecar: A Domain-Specific Approach to Writing Secure Database Migrations** appearing in PLDI '21.

## Abstract
Web applications often handle large amounts of sensitive user data.  Modern secure web frameworks protect this data by (1) using declarative languages to specify security policies alongside database schemas and (2) automatically enforcing these policies at runtime.  Unfortunately, these frameworks do not handle the very common situation in which the schemas or the policies need to evolve over time---and updates to schemas and policies need to be performed in a carefully coordinated way.  Mistakes during schema or policy migrations can unintentionally leak sensitive data or introduce privilege escalation bugs.  In this work, we present a domain-specific language (Scooter) for expressing schema and policy migrations, and an associated SMT-based verifier (Sidecar) which ensures that migrations are secure as the application evolves.  We describe the design of Scooter and Sidecar and show that our framework can be used to express realistic schemas, policies, and migrations, without giving up on runtime or verification performance.

## Repository Map

- [`cli`] - Implements the `migrate` command that's used for executing migrations

- [`mongodb-enforcement`] - Contains the runtime enforcement (including codegen) for enforcing policies during program execution

- [`mongodb-migrate`] - Contains the logic to perform migrations against a mongodb database ([`cli`] relies on this)

- [`static-checker`] - Implements SMT-based checking of policies and policy functions to ensure that new policies are stricter than old policies.

- [`policy-lang`] - Implements parser, name resolution, and type-checker for the policy language (including migration).

- [`web-demo`] - A small rocket web-server that leverages `static-checker` to power a playground. This sub-project also includes a small wasm binding layer for client-side parsing in the playground

[`cli`]: ./cli
[`mongodb-enforcement`]: ./mongodb-enforcement
[`mongodb-migrate`]: ./mongodb-migrate
[`static-checker`]: ./static-checker
[`policy-lang`]: ./policy-lang
[`web-demo`]: ./web-demo
