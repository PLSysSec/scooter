## Enforcement

This crate is responsible for two things:
1. Generating rust types for each collection in your policy
2. Ensuring policies are not violated during program runtime

## 1. Generating rust types
Your `policy.txt` file is the authoritative source of both your schema and
policy. In order to avoid possibly mismatched re-declarations in your rust
code, the `enforcement` crate will generate the appropriate rust types for
you.

To take advantage of this feature, first add `enforcement` to your
`Cargo.toml` as a build-dependency:

```toml
[build-dependency]
enforcement = ...
```

Then in your `build.rs`:

```rust
use enforcement::translate;

fn main() {
    translate::translate_policy_file("policy.txt", "schema.rs");
}
```

Lastly, create a `schema.rs` in your `src` directory:

```rust
include!(concat!(env!("OUT_DIR"), "/types.rs"));
```

This setup will ensure that your rust types always match your `policy.txt`


## 1. Runtime Enforcement

Consider the following policy:
```
User {
    create: public,
    delete: public,

    name: String {
        read: public,
        write: public,
    }
}
```

`enforcement` will generate the following type:

```rust
pub struct User {
    name: String
}
```

**Note that the member is private!**
If we allowed direct access, we couldn't enforce the policies at runtime. More on this later

All collection structs implement the `DBCollection` which is a trait that
provides basic DB access:

```rust
pub trait DBCollection: Sized {
    type Partial;
    fn find_by_id(connection: &AuthConn, id: RecordId) -> Option<Self::Partial>;
    fn find_all(connection: &AuthConn) -> Option<Vec<Self::Partial>>;
    fn find_full_by_id(connection: &DBConn, id: RecordId) -> Option<Self>;
    fn insert_one(connection: &AuthConn, item: Self) -> Option<TypedRecordId<Self>>;
    fn insert_many(connection: &AuthConn, items: Vec<Self>) -> Option<Vec<TypedRecordId<Self>>>;
    fn save_all(connection: &AuthConn, items: Vec<&Self::Partial>) -> bool;
    fn delete_by_id(connection: &AuthConn, id: RecordId) -> bool;
}
```

so for example:

```rust
let x: User::Partial = User::find_by_id(conn, some_id).unwrap();
```

Will fetch the user associated with `some_id`, on behalf of the authenticated user.
Every `DBCollection` has an associated `Partial` type which is the same as the underlying struct except every field is `pub` and optional. So `User::Partial` looks like this:

```rust
struct UserPartial {
    pub name: Option<String>
}
```

If the principal associated with `conn` is unable to read the `name` field of this particular user, the value of `name` will be `None`. **Note that direct access is allowed because the permissions have been fully resolved**

This approach is less efficient than resolving just the fields you need. For
performance-critical applications, you can use the getters and setters on the
`User` struct itself.


## Creating new objects
Because the fields of our `User` struct are private, you can't just create your own.
For this reason, we provide a `user!` macro that allows the creation of objects (that you will presumably save to the database later).

```rust
let x: User = user! {
    name: "Foo"
};
```
