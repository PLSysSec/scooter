# Simple Messaging

## Iteration 1. Direct Messaging

In this iteration, messages are immutable 1-1 communications. They cannot be deleted either.

### Migration
```
createCollection("User", {
    username: String,
    passHash: String
})

createCollection("Message", {
    message: String,
    from: Id("User")
    to: Id("User")
})
```

### Policy
```
User:
    create: public,
    delete: u -> u.id

User {
    username: 
        read: public
        write: u -> u.id 
    passHash: 
        read: u -> u.id
        write: u -> u.id
}

Message:
    create: m -> [m.from]
    delete: none


Message {
    message: 
        read: m -> [m.from, m.to]
        write: none
    from: 
        read: m -> [m.from, m.to]
        write: none
    to:
        read: m -> [m.from, m.to]
        write: none
}
```

## Iteration 2. Deleting messages

We want users to be able to delete messages they receive. But notably this shouldn't hide them from the sender.

### Migration
```
// There will now be a copy of each message for each recipient
Message.addField("owner", Id("User"), m -> m.from)

// Copy the message for each recipient
Message.forEach(m -> 
    Message.create({
        owner: m.to,
        ...m
    })
)
```


### Policy
Due to the migration we know that m.owner = `m.to` v `m.from`.
Thus all the field permissions on Message are allowed because:
`m.to` ^ `m.from` => `m.to` v `m.from`. That is, the policy is less strict.
However, the delete permission is a new grant.


```
User:
    create: public,
    delete: u -> u.id

User {
    username: 
        read: public
        write: u -> u.id 
    passHash: 
        read: u -> u.id
        write: u -> u.id
}

Message:
    create: m -> [m.from]
    delete: m -> [m.owner] !!!grant!!!

Message {
    message: 
        read: m -> [m.owner]
        write: none
    from: 
        read: m -> [m.owner]
        write: none
    to:
        read: m -> [m.owner]
        write: none
    owner:
        read: m -> [m.owner]
        write: none
}
```


## Iteration 3. Multiple Recipients (cc)

### Migration

```
// changeField<T> Key -> T -> (Record -> T)
Message.changeField("to", [Id("User")], m -> [m.from])
```

### Policy

No change!
```
User:
    create: public,
    delete: u -> u.id

User {
    username: 
        read: public
        write: u -> u.id 
    passHash: 
        read: u -> u.id
        write: u -> u.id
}

Message:
    create: m -> [m.from]
    delete: m -> [m.owner]

Message {
    message: 
        read: m -> [m.owner]
        write: none
    from: 
        read: m -> [m.owner]
        write: none
    to:
        read: m -> [m.owner]
        write: none
    owner:
        read: m -> [m.owner]
        write: none
}
```


## Iteration 4. Private Messages (bcc)

### Migration

```
// addField<T> Key -> T -> (Record -> T)
Message.addField("bcc", [Id("User")], m -> [])
```

### Policy

You can only read the bcc field if you are both the sender and the owner.
This migration is allowable because all data in bcc is public (not derived from any db value)

```
User:
    create: public,
    delete: u -> u.id

User {
    username: 
        read: public
        write: u -> u.id 
    passHash: 
        read: u -> u.id
        write: u -> u.id
}

Message:
    create: m -> [m.from]
    delete: m -> [m.owner]

Message {
    message: 
        read: m -> [m.owner]
        write: none
    from: 
        read: m -> [m.owner]
        write: none
    to:
        read: m -> [m.owner]
        write: none
    bcc:
        read: m -> [m.owner] U [m.from]
        write: 
    owner:
        read: m -> [m.owner]
        write: none
}
```


# Twitter

## Iteration 1. All public

All tweets are public. No followers

### Migration
```
createCollection("User", {
    handle: String,
    passHash: String
})

createCollection("Tweet", {
    message: String,
    author: Id("User")
})
```

### Policy

```
User:
    create: public,
    delete: u -> u.id

User {
    handle: 
        read: public
        write: u -> u.id 
    passHash: 
        read: u -> u.id
        write: u -> u.id
}


Tweet:
    create: t -> t.author
    delete: t -> t.author

Tweet {
    author:
        write: none
        read: public
    message:
        write: t -> t.author
        read: public
}
```


## Iteration 2. Followers

In this iteration we want to introduce followers which are visible to all.
Followers are now only used for aggregating a feed, no permissions are granted
by being a follower.

Due to the possible size of a followers list, we'll make it a separate DB element.

### Migration

```
createCollection("Follow", {
    target: Id("User"),
    owner: Id("User")
})
```

### Policy
We allow all users to see who's following whom.

```
User:
    create: public,
    delete: u -> u.id

User {
    handle: 
        read: public
        write: u -> u.id 
    passHash: 
        read: u -> u.id
        write: u -> u.id
}


Tweet:
    create: t -> t.author
    delete: t -> t.author

Tweet {
    author:
        write: none
        read: public
    message:
        write: t -> t.author
        read: public
}

Follow:
    create: f -> f.owner
    delete: f -> f.owner

Follow {
    owner:
        write: none
        read: public
    target:
        write: none
        read: public
}
```

## Iteration 3. Blocking

People have noticed there are some undesirable interactions happening on the site.
They want to start blocking folks.

### Migration

```
createCollection("Blocks", {
    target: Id("User"),
    owner: Id("User")
})
```

### Policy
The policy language currently can't support negations so this will have to be
enforced in the application code. This is due to decidability issues.

[TBD]