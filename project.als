// 1. structure of the social network, includes users and friendships
sig User {}
sig Wall {}

abstract sig Content {
	ViewPrivacy: one PrivacyLevel,
       CommentPrivacy: one PrivacyLevel
}
sig Note extends Content {
	contains : some Photo
}
sig Photo extends Content {}
sig Comment extends Content {}
sig Nicebook {

	users: set User,				// registered users
	contents: set Content,			// contents in Nicebook

	friends: users -> users,			// friends of a user
	walls: users -> one Wall, 			// user's wall
	own: users -> contents,			// content uploaded by the user

	published: Wall -> contents,		// published content on the wall
	wallPrivacy: Wall -> one PrivacyLevel,	// wall's privacy level

	comments: contents -> Comment, 	// content's attached comments
	tags: contents -> users,			// tags in the content
}

abstract sig PrivacyLevel{}
one sig OnlyMe, Friends, FriendsOfFriends, Everyone extends PrivacyLevel{}

pred userInScope [n: Nicebook, u: User] {
	u in n.users
}
pred contentInScope [n: Nicebook, c: Content] {
	c in n.contents
}

/////////////// PUBLISH and UNPUBLISH ///////////////
// publish a piece of content on a user’s wall. The content may be the existing one. 
pred publish [n, n' : Nicebook, u : User, c : Content,
			 viewPrivacy: PrivacyLevel, commentPrivacy: PrivacyLevel] {
	n'.users = n.users
	n'.contents = n.contents
	n'.friends = n.friends
	n'.walls = n.walls
	n'.comments = n.comments
	n'.tags = n.tags
	n'.wallPrivacy = n.wallPrivacy	

       //the user should be a registered user
	// the content should be in nicebook
	userInScope[n, u] and contentInScope[n, c]

	//the content should not has been published by any user in the nicebook
	c not in n.users.(n.walls).(n.published)

	//if the content c is a new content
       c not in (n.users).(n.own)
		implies 
			//we should upload it first
			n'.own = n.own + (u -> c) and 
			//and set its viewPrivacy level
			c.ViewPrivacy = viewPrivacy and
			//and set its commentPrivacy level
			c.CommentPrivacy = commentPrivacy
		else
			//otherwise, c is an existing content, then do nothing
			n'.own = n.own

	n'.published = n.published + 
			//add the content to user self's wall
			(u.(n.walls) -> c) + 
			//add the content to all taged users' wall
			(n.walls[n.tags[c]] -> c)
}
assert publishPreserveInv {
	all n, n': Nicebook, u: User, c: Content,
		vPrivacy: PrivacyLevel, cPrivacy:  PrivacyLevel |
			invariants[n] and publish[n, n', u, c, vPrivacy, cPrivacy]
			implies invariants[n']
} check publishPreserveInv

// hide a piece of content on a user’s wall
pred unpublish [n, n' : Nicebook, u : User, c : Content] {

	// only the owner can hide the content on his/her and related user's wall
	n'.users = n.users
	n'.contents = n.contents
	n'.friends = n.friends
	n'.own = n.own
	n'.walls = n.walls
	n'.comments = n.comments
	n'.tags = n.tags
	n'.wallPrivacy = n.wallPrivacy

       //the user should be a registered user
	// the content should be in nicebook
	userInScope[n, u] and contentInScope[n, c]

       //the content should be owned by the user
	c in u.(n.own)
       //the content should has been published
       c in u.(n.walls).(n.published)

	n'.published = n.published - 
                            //remove the content from user self's wall
				(u.(n.walls) -> c) - 
                            //remove the content from all taged users' wall
				(n.walls[n.tags[c]] -> c)
}
assert unpublishPreserveInv {
	all n, n': Nicebook, u: User, c: Content |
		invariants[n] and unpublish[n, n', u, c] implies invariants[n']
} check unpublishPreserveInv

/////////////// UPLOAD and REMOVE ///////////////
// Upload a piece of content, excluding the attached comments
pred upload [n, n': Nicebook, u: User, c: Content, vPrivacy: PrivacyLevel, cPrivacy: PrivacyLevel] {
	// precondition
	userInScope[n, u] and contentInScope[n, c]
	// the content doesn't exist
	c not in n.own[n.users]

	// postcondition
	// the content belongs to the user
	n'.own = n.own + (u -> c)
	// set privacy of the content
	c.ViewPrivacy = vPrivacy
	c.CommentPrivacy = cPrivacy
	n'.contents = n.contents + c

	n'.users = n.users
	n'.friends = n.friends
	n'.walls = n.walls
	n'.published = n.published
	n'.wallPrivacy = n.wallPrivacy
	n'.comments = n.comments
	n'.tags = n.tags
}
assert uploadPreserveInv {
	all n, n': Nicebook, u: User, c: Content,
		vPrivacy: PrivacyLevel, cPrivacy:  PrivacyLevel |
			invariants[n] and upload[n, n', u, c, vPrivacy, cPrivacy]
			implies invariants[n']
} check uploadPreserveInv

// Remove an existing piece of content from a user’s account.
pred remove [n, n': Nicebook, u: User, c: Content] {
	// precondition
	userInScope[n, u] and contentInScope[n, c]
	// the content must belong to the user
	c in n.own[u]

	// postcondition
	// remove the content form the user
	n'.own = n.own - (u -> c)
	// remove from owner's and tagged users' published
	n'.published = n.published - (n.walls[u + n.tags[c]] -> c)
	// remove the attached comments
	n'.comments = n.comments - (c -> n.comments[c])
	// remove tags of the content
	n'.tags = n.tags - (c -> n.tags[c])
	// remove attached comments
	n'.contents = n.contents - c - n.comments[c]
	// if c belongs to some note, should remove it
	one content, content': n.contents |
		(c in content.contains) implies (content'.contains = content.contains - c)

	n'.users = n.users
	n'.friends = n.friends
	n'.walls = n.walls
	n'.wallPrivacy = n.wallPrivacy
}
assert removePreserveInv {
	// TODO has counterexample because of publishInvariant
	all n, n': Nicebook, u: User, c: Content |
		invariants[n] and remove[n, n', u, c] implies invariants[n']
} check removePreserveInv for 10

/////////////// ADD COMMENT ///////////////
// Add a comment to a content.
pred addComment [n, n': Nicebook, u: User, comment: Comment, content: Content] {
	// precondition
	userInScope[n, u] and contentInScope[n, comment] and
	contentInScope[n, content]
	// comment not own by any user
	comment not in n.own[n.users]
	// the comment doesn't exist
	comment not in n.comments[n.contents]
	// authorized to add comment to the content
	content in commentable[n, u]

	// postcondition
	n'.comments = n.comments + (content -> comment)
	// the comment must belong to the user
	n'.own = n.own + (u -> comment)
	// the comment is attached to the content
	n'.comments = n.comments + (content -> comment)
	// comment's privacy must be same as the attached content
	comment.ViewPrivacy = content.ViewPrivacy
	comment.CommentPrivacy = content.CommentPrivacy
	n'.contents = n.contents + comment

	n'.users = n.users
	n'.friends = n.friends
	n'.walls = n.walls
	n'.published = n.published
	n'.wallPrivacy = n.wallPrivacy
	n'.tags = n.tags
}
assert addCommentPreserveInv {
	all n, n': Nicebook, u: User, c: Content , comment: Comment| 
		invariants[n] and addComment[n, n', u, comment, c]
		implies invariants[n']
} check addCommentPreserveInv for 10

/////////////// ADD TAG & REMOVE TAG ///////////////
// add a tag to a note or photo
pred addTag[n, n' : Nicebook, u1, u2 : User, c : Content] {
	// u1 is the user who launched the "addTag" action
	// u2 is the user who is tagged by u1
	// precondition: 
	// both users u1 and u2 are users in nicebook n
	userInScope[n, u1]
	userInScope[n, u2]
	// user who tags another user must be that user's friend, i.e., 
	// u1 should be a friend of u2(tagged user)
	// also that user cannot be tagged by himself as user cannot be his own friend
	(u1 in n.friends[u2])
	// the content to be tagged must be published on some wall
	some (n.published).c
	// only photo and note can be tagged
	c not in Comment
	
	// postcondition:
	// content is added to the wall of user and tag is added to the content
	n'.published = n.published + u2.(n.walls)->c
	n'.tags = n.tags + (c -> u2)

	// nothing else changes 
	n'.users = n.users
	n'.friends = n.friends
	n'.own = n.own
	n'.walls = n.walls
	n'.comments = n.comments
	n'.wallPrivacy = n.wallPrivacy
}
assert addTagPreservesInvariant {
	all n, n' : Nicebook, u1,u2 : User, c : Content |
		invariants[n] and addTag[n, n', u1, u2, c] implies
			invariants[n']
} check addTagPreservesInvariant for 7

// remove a tag on a note or photo
pred removeTag[n, n' : Nicebook, u : User, c : Content] {
	// precondition:
	// user u is a user in nicebook n
	userInScope[n, u]
	// content c must be present in tagged user's wall 
	c in (u.(n.walls)).(n.published)
	
	// postcondition:
	// user (who removes tag) can either be the owner of that post or tagged to that post
	
	// content is removed from the wall of user and tag is removed from the content
	u in n.tags[c] implies 
	n'.published = n.published - (u.(n.walls))->c and
	n'.tags = n.tags - (c -> u)

	// owner removes tag of a user from content
	(one n.(own.c) and u in n.tags[c]) implies
	(n'.published = n.published - (u.(n.walls))->c and
	n'.tags = n.tags - (c -> u))

	//nothing else changes 
	n'.users = n.users
	n'.friends = n.friends
	n'.own = n.own
	n'.walls = n.walls
	n'.comments = n.comments
	n'.wallPrivacy = n.wallPrivacy
}
assert removeTagPreservesInvariant {
	all n, n' : Nicebook, u : User, c : Content |
		invariants[n] and removeTag[n, n', u, c]
		implies invariants[n']
} check removeTagPreservesInvariant for 7

/////////////// PRIVACY ///////////////
pred setContentPrivacy[n, n' : Nicebook, u : User, c, c' : Content, p : PrivacyLevel] {
	// precondition
	userInScope[n, u] and contentInScope[n, c]
	// only the content's owner can change its viewPrivacy
	(u -> c) in n.own
	// postcondition
	c'.ViewPrivacy = p
	n'.own = n.own - u -> c + u -> c'
}
assert setContentPrivacyPreservesInvariant {
	all n, n' : Nicebook, u : User, c, c' : Content, p : PrivacyLevel |
		invariants[n] and setContentPrivacy[n, n', u, c, c', p]
		implies invariants[n']
} check setContentPrivacyPreservesInvariant for 7

pred setCommentPrivacy[n, n' : Nicebook, u : User, c, c' : Content, p : PrivacyLevel] {
	// precondition
	userInScope[n, u] and contentInScope[n, c]
	// only the content's owner can change its commentPrivacy
	(u -> c) in n.own
	// postcondition
	c'.CommentPrivacy = p
	n'.own = n.own - u -> c + u -> c'
}
assert setCommentPrivacyPreservesInvariant {
	all n, n' : Nicebook, u : User, c, c' : Content, p : PrivacyLevel |
		invariants[n] and setCommentPrivacy[n, n', u, c, c', p]
		implies invariants[n']
} check setCommentPrivacyPreservesInvariant for 7

fun commentable [n : Nicebook, u : User] : set Content{
	// return the contents that the user can comment
	{ c : n.contents | userInScope[n, u] and (
				(c.CommentPrivacy = OnlyMe and n.own.c = u) or
				(c.CommentPrivacy = Friends and u in (n.friends[n.own.c] + n.own.c) and c in n.published[Wall]) or
				(c.CommentPrivacy = FriendsOfFriends and u in (n.friends[n.friends[n.own.c]] + n.friends[n.own.c] + n.own.c) and c in n.published[Wall]) or
				(c.CommentPrivacy = Everyone and c in n.published[Wall])) }
}
fun viewable [n : Nicebook, u: User] : set Content{
	// return the content that can be viewed by the user
	// TODO also the content unpublished but owned by the user?
	{ c : n.contents | userInScope[n, u] and (
		(c.ViewPrivacy = OnlyMe and n.own.c = u) or
		(c.ViewPrivacy = Friends and u in (n.friends[n.own.c] + n.own.c) and c in n.published[Wall]) or
		(c.ViewPrivacy = FriendsOfFriends and u in (n.friends[n.friends[n.own.c]] + n.friends[n.own.c] + n.own.c) and c in n.published[Wall]) or
		(c.ViewPrivacy = Everyone and c in n.published[Wall])) }
}

pred publishInvariant[n : Nicebook] {
	// TODO it's weird that unpublished content but also owned by the user cannot see it
	all u : n.users | all c : n.contents | (c not in n.published[Wall] 
	and u not in n.own.c) implies c not in viewable[n, u]
}

pred privacyWallContentInvariant[n : Nicebook, w : Wall, c : Content] {
	//the content privacy level is no lower than the wall privacy level
	n.wallPrivacy[w] = OnlyMe implies c.ViewPrivacy = OnlyMe and c.CommentPrivacy = OnlyMe
	n.wallPrivacy[w] = Friends implies c.ViewPrivacy in Friends + OnlyMe and c.CommentPrivacy in Friends + OnlyMe
	n.wallPrivacy[w] = FriendsOfFriends implies c.ViewPrivacy in (FriendsOfFriends + Friends + OnlyMe) and c.CommentPrivacy in (FriendsOfFriends + Friends + OnlyMe)
	n.wallPrivacy[w] = Everyone implies c.ViewPrivacy = PrivacyLevel and c.CommentPrivacy = PrivacyLevel
}

pred ViewPrivacyInvariant[n : Nicebook] {
	all c : n.contents | all u : n.users | (c.ViewPrivacy = OnlyMe and u != n.own.c implies c not in viewable[n, u]) and
						     (c.ViewPrivacy = Friends and u not in (n.own.c + n.friends[u]) implies c not in viewable[n, u]) and
						     (c.ViewPrivacy = FriendsOfFriends and u not in (n.own.c + n.friends[u] + n.friends[n.friends[u]]) implies c not in viewable[n, u])
}

pred CommentPrivacyInvariant[n : Nicebook] {
	all c : n.contents | all u : n.users | (c.CommentPrivacy = OnlyMe and u != n.own.c implies c not in commentable[n, u]) and
						     (c.CommentPrivacy = Friends and u not in (n.own.c + n.friends[u]) implies c not in commentable[n, u]) and
						     (c.CommentPrivacy = FriendsOfFriends and u not in (n.own.c + n.friends[u] + n.friends[n.friends[u]]) implies c not in commentable[n, u])
}

/////////////// INVARIANTS ///////////////
pred contentInvariant [c: Content, n: Nicebook] {
	// the content belongs to only one user
	one u: n.users | c in n.own[u]
	// preventing comment circularity
	c not in c.^(n.comments)
	// the note and its containing photos have same owner
	(c in Note and c.contains != none) implies (n.own.c = n.own.(c.contains))
	// an attached comment can only be attached to 1 content
	(c in n.comments[n.contents]) implies (one n.comments.c)
}
pred wallInvariant[n : Nicebook] {
	// every user has a wall
	all u: n.users | one n.walls[u]
	// different users have different walls
	all u1, u2: n.users | (u1 != u2) iff (n.walls[u1] != n.walls[u2])
	//one n.walls.Wall // this may cause no instance found [TODO]
	// TODO attached comments should not be shown on owner's wall
	all c : Comment, u : User | 
	((u in (n.own).c) and (c not in ((n.own[u]).(n.comments)))) 
	implies
	c not in n.published[n.walls[u]]
	// the content published on someone's wall
	// should be owned by the user or be tagged
	all u: n.users | all c: n.published[n.walls[u]] |
		(c in n.own[u]) or (u in n.tags[c])
}
pred userInvariant[n: Nicebook] {
	// a user cannot be his/her own friend
	all u : n.users | u not in n.friends[u]
	// if u1 is a friend of u2, then u2 is also a friend of u1
	all u1, u2 : n.users | (u1 != u2 and u2 in n.friends[u1]) implies u1 in n.friends[u2]
}
pred tagInvariant [n: Nicebook] {
	// the tag cannot be attached to comment
	no u: n.users | u in n.tags[Comment]
}

pred invariants [n: Nicebook] {
	all n': Nicebook, u: User, c: Content, vPrivacy: PrivacyLevel, cPrivacy:  PrivacyLevel |
		publish[n, n', u, c, vPrivacy, cPrivacy]
	all n': Nicebook, u: User, c: Content |
		unpublish[n, n', u, c]
	all n': Nicebook, u: User, c: Content, vPrivacy: PrivacyLevel, cPrivacy:  PrivacyLevel |
		upload[n, n', u, c, vPrivacy, cPrivacy]
	all n': Nicebook, u: User, c: Content |
		remove[n, n', u, c]
	all n': Nicebook, u: User, c: Content , comment: Comment| 
		addComment[n, n', u, comment, c]
	all n' : Nicebook, u1, u2: User, c : Content | 
		addTag[n, n', u1, u2, c]
	all n' : Nicebook, u : User, c : Content | 
		removeTag[n, n', u, c]
	all n' : Nicebook, u : User, c, c' : Content, p : PrivacyLevel |
		setContentPrivacy[n, n', u, c, c', p]
	all n' : Nicebook, u : User, c, c' : Content, p : PrivacyLevel |
		setCommentPrivacy[n, n', u, c, c', p]

	publishInvariant[n]
	all w : Wall, c : n.contents | privacyWallContentInvariant[n, w, c]
	ViewPrivacyInvariant[n]
	CommentPrivacyInvariant[n]
	all c: n.contents | contentInvariant[c, n]
	wallInvariant[n]
	userInvariant[n]
	tagInvariant[n]
}

run {
	all n: Nicebook | invariants[n]
} for 3
