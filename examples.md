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

Message {
    create: m -> [m.from]
    delete: none
}

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
// changeField<T> Key -> T -> (Record -> T)
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