export const examples = {
  "Leaking with AddField": {
    policy: `# Here is an example Scooter policy.
# The policy represents the schema and security policy at a given point in time.
# We update policies using migrations (see the top-right "Migration" box).

# This is the definition of a model for users of a web-application
# Unlike a typical ORM model, this definition includes policies for:
#	- creating a User
#	- deleting a User
#	- reading a field
#	- writing a field
@principal
User {
	# Anyone can create a user
	create: public,

	# No one can delete a user (hey, this is just an example)
	delete: none,

	# Users have an email which is a String
	email: String {

		# Policies are defined using policy functions which answer the question:
		#     "For a given record, who can read/write/create/delete"?
		#
		# In this case, for a given user, only that user may read the email field
		read: user -> [user.id],

		# Similarly, a user's email may only be modified by that user.
		write: user -> [user.id],
	},
}`,
    migration: `# In this migration, we are giving all users a public "bio".
# We unsafely populate the bio using the user's email which is private.
#
# Click the "Run Migration" button to see how Sidecar catches this bug.

User::AddField(
	bio: String {
		read: public,
		write: user -> [user.id],
	},

	# When we add a field, we also provide a function to populate it
	# This function leaks private data.
	# Try changing it to make the migration successful.
	user -> "Hi, my email is: " + user.email
)`,
  },

  "Principaled Principals": {
	migration: "",
	policy: `# Scooter expresses policies in terms of "principals"
# Scooter expresses policies in terms of "principals"
# which represent entities which may access the database.
# In many applications, the only kind of principal is a User, but sometimes
# requests are made by third-party applications, or internal infrastructure like
# a CRON job, or authentication system; these are all principals.

# In Scooter, principals are either static values:

@static-principal
CronJob

# or database ids:

@principal
User {
	create: public,

	# Policy functions are well-typed and always return a set of principals.
	# Try commenting out the @principal above to see the type error.
	delete: user -> [user.id, CronJob],
}

# We can have as many of each kind of principal as we want

@principal
Team {
    create: _ -> User::Find({}).map(u -> u.id),
    delete: team -> team.members,


    members: Set(Id(User)) {
        read: public,

        # Here we allow both the team as a principal and the members to edit membership
        # when the web application makes a request to the database, it will have to pick
        # which principal to associate with the request.
        write: team -> [team.id] + team.members,
    },
}


# Note: Scooter has an implicit Unauthenticated principal that can only access
#       public data. It cannot be mentioned in policy functions to ensure that
#       Unauthenticated never gains more permissions than a normal principal`
  }
};
