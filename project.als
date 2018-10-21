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
pred upload [n, n': Nicebook, u: User, c: Content] {
	// precondition
	// the content doesn't exist
	c not in n.own[u]

	// postcondition
	// the content belongs to the user
	c in n'.own[u]
	// the privacy level is same as the wall's privacy TODO wait for Olivia
	c.ViewPrivacy = n'.wallPrivacy[n'.walls[u]]
	// the content is shown on the user's wall
	c in n'.published[n'.walls[u]]
	// TODO the owner should also be tagged in the uploaded content
	//c in Note or c in Photo implies (u in b'.references[b'.tags[c]])
	nothingChanged[n, n']
}

// Remove an existing piece of content from a user’s account.
pred remove [n, n': Nicebook, u: User, c: Content] {
	// precondition
	// the content must belong to the user
	c in n.own[u]

	// postcondition
	// remove the attached comments
	n'.comments[c] = none
	// remove the tags
	n'.tags[c] = none
	// remove the content form the user
	c not in n'.own[u]
	// remove the content form the wall
	c not in n'.published[n'.walls[u]]
}

fun commentable [n : Nicebook, u : User] : set Content{
	// return the contents that the user 
	{ c : Content | (c.CommentPrivacy = OnlyMe and n.own.c = u) or
			     (c.CommentPrivacy = Friends and u in n.friends[n.own.c] + n.own.c) or
			     (c.CommentPrivacy = FriendsOfFriends and u in n.friends[n.friends[n.own.c]] + n.friends[n.own.c] + n.own.c) or
			     (c.CommentPrivacy = Everyone) }	
}

// Add a comment to a content.
pred addComment [n, n': Nicebook, u: User, comment: Comment, content: Content] {
	// precondition
	// the comment doesn't exist
	comment not in n.comments[content]
	// authorized to add comment to the content
	// TODO from Olivia

	// postcondition
	// the comment must belong to the user
	comment in n'.own[u]
	// the comment is attached to the content
	comment in n'.comments[content]
}

assert uploadPreserveInv {
	all n, n': Nicebook, u: User, c: Content | 
		invariants[n] and upload[n, n', u, c] implies invariants[n']
}
check uploadPreserveInv for 10

assert removePreserveInv {
	all n, n': Nicebook, u: User, c: Content | 
		invariants[n] and remove[n, n', u, c] implies invariants[n']
}
//check removePreserveInv for 10

assert addCommentPreserveInv {
	all n, n': Nicebook, u: User, c: Content , comment: Comment| 
		invariants[n] and addComment[n, n', u, comment, c] implies invariants[n']
}
//check addCommentPreserveInv for 10

pred userInvariant [u: User, n: Nicebook] {
	// a user cannot be his/her own friend
	u not in n.friends[u]
	// if u1 is a friend of u2, then u2 is also a friend of u1
	all u1, u2 : User | (u1 != u2 and u2 in n.friends[u1]) implies u1 in n.friends[u2]
}

pred tagInvariant [t: Tag, n: Nicebook] {
	// the tag cannot be attached to comment
	no t: Tag | t in n.tags[Comment]
}

pred contentInvariant [c: Content, n: Nicebook] {
	// the content belongs to only one user
	one u: User | c in n.own[u]
}

pred invariants [n: Nicebook] {
	all u: User | userInvariant[u, n]
	all c: Content | contentInvariant[c, n]
	all t: Tag | tagInvariant[t, n]
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
} for 3 but exactly 1 Nicebook, exactly 2 User, exactly 5 Content
