// 1. structure of the social network, includes users and friendships
sig User {}
sig Tag {}
sig Wall {}

abstract sig Content {
	ViewPrivacy: one PrivacyLevel,
       CommentPrivacy: one PrivacyLevel
}
sig Note extends Content {
	contains : some Photo,
	associatedWith : some Tag
}
sig Photo extends Content {
	associatedWith : some Tag
}
sig Comment extends Content {
	attachedTo: one Content
}

sig Nicebook {

	users: User,					// registered users

	friends: User -> User,			// friends of a user
	walls: User -> one Wall, 			// user's wall
	own: User -> Content,			// content uploaded by the user
	view: User -> Content, 			// viewable content to an user

	published: Wall -> Content,		// published content on the wall
	wallPrivacy: Wall -> PrivacyLevel,	// wall's privacy level

	comments: Content -> Comment, 	// content's attached comments
	tags: Content -> Tag,			// tags in the content

	references: Tag -> one User,		// tag reference to an user
}

abstract sig PrivacyLevel{}

one sig OnlyMe, Friends, FriendsOfFriends, Everyone extends PrivacyLevel{}

pred nothingChanged[n, n' : Nicebook]{
	n'.friends = n.friends
	n'.own = n.own
	n'.walls = n.walls
	n'.comments = n.comments
	n'.tags = n.tags
	n'.view = n.view
	n'.references = n.references
	n'.published = n.published
	n'.wallPrivacy = n.wallPrivacy
}

// publish a piece of content on a user’s wall. The content may be the existing one. 
pred publish [u : User, c : Content, n,n' : Nicebook] {

	n'.users = n.users
	n'.friends = n.friends
	n'.own = n.own
	n'.walls = n.walls
	n'.comments = n.comments
	n'.tags = n.tags
	n'.view = n.view
	n'.references = n.references
//	n'.published = n.published
	n'.wallPrivacy = n.wallPrivacy	

	(
		(u in n.users) 
			and
	      	(c not in n.users.(n.walls).(n.published))
	)
		implies
	n'.published = n.published + 
				(u.(n.walls) -> c) + 
				(c.(n.tags).(n.references).(n.walls) -> c)

	(
		(u not in n.users)
			or 
		(c in n.users.(n.walls).(n.published))
	)
		implies
	n'.published = n.published
	
}

// hide a piece of content on a user’s wall
pred unpublish [u : User, c : Content, n,n' : Nicebook] {

	// only the owner can hide the content on his/her and related user's wall
	n'.users = n.users
	n'.friends = n.friends
	n'.own = n.own
	n'.walls = n.walls
	n'.comments = n.comments
	n'.tags = n.tags
	n'.view = n.view
	n'.references = n.references
//	n'.published = n.published
	n'.wallPrivacy = n.wallPrivacy

	(
		(u in n.users) and (c in u.(n.own))
	)
		implies
	n'.published = n.published - 
				(u.(n.walls) -> c) - 
				(c.(n.tags).(n.references).(n.walls) -> c)

	(		
		(u not in n.users) or (c not in u.(n.own))
	)
		implies
	n'.published = n.published
}

// Upload a piece of content, excluding the attacked comments
pred upload [b, b': Nicebook, u: User, c: Content] {
	// precondition
	// the content doesn't exist
	c not in b.own[u]

	// postcondition
	// the content belongs to the user
	c in b'.own[u]
	// the privacy level is Everyone
	c.ViewPrivacy = Everyone
	// the content is shown on the user's wall
	c in b'.published[b'.walls[u]]
}

// Remove an existing piece of content from a user’s account.
pred remove [b, b': Nicebook, u: User, c: Content] {
	// precondition
	// the content must belong to the user
	c in b.own[u]

	// postcondition
	// remove the attached comments
	b'.comments[c] = none
	// remove the tags
	b'.tags[c] = none
	// remove the content form the user
	c not in b'.own[u]
	// remove the content form the wall
	c not in b'.published[b'.walls[u]]
}

// Add a comment to a content.
pred addComment [b, b': Nicebook, u: User, comment: Comment, content: Content] {
	// precondition
	// the comment doesn't exist
	comment not in b.comments[content]
	// authorized to add comment to the content
	// TODO from Olivia

	// postcondition
	// the comment must belong to the user
	comment in b'.own[u]
	// the comment is attached to the content
	comment in b'.comments[content]
}

assert uploadPreserveInv {
	all b, b': Nicebook, u: User, c: Content | 
		invariants[b] and upload[b, b', u, c] implies invariants[b']
}
check uploadPreserveInv for 10

assert removePreserveInv {
	all b, b': Nicebook, u: User, c: Content | 
		invariants[b] and remove[b, b', u, c] implies invariants[b']
}
check removePreserveInv for 10

assert addCommentPreserveInv {
	all b, b': Nicebook, u: User, c: Content , comment: Comment| 
		invariants[b] and addComment[b, b', u, comment, c] implies invariants[b']
}
check addCommentPreserveInv for 10

pred userInvariant [u: User, b: Nicebook] {
	// if u1 is a friend of u2, then u2 is also a friend of u1
	all u1, u2 : User | u1 != u2 and u1 in b.friends[u1] implies u2 in b.friends[u1]
}

pred tagInvariant [t: Tag, b: Nicebook] {
	// the tag cannot be attached to comment
	no t: Tag | t in b.tags[Comment]
}

pred contentInvariant [c: Content, b: Nicebook] {
	// the content belongs to only one user
	one u: User | c in b.own[u]
}

pred invariants [b: Nicebook] {
	all u: User | userInvariant[u, b]
	all c: Content | contentInvariant[c, b]
	all t: Tag | tagInvariant[t, b]
}

/* privacy setting
fun viewable [u: User] {
	// return the content that can be viewed by the user
}

assert NoPrivacyViolation {
	// violation occurs if a user is able to see content not in `viewable`
}
*/

run {
	all b: Nicebook | invariants[b]
}
