// 1. structure of the social network, includes users and friendships
sig User {}
sig Tag {}
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

	users: User,					// registered users

	friends: users -> users,			// friends of a user
	walls: users -> one Wall, 			// user's wall
	own: users -> Content,			// content uploaded by the user

	published: Wall -> Content,		// published content on the wall
	wallPrivacy: Wall -> one PrivacyLevel,	// wall's privacy level

	comments: Content -> Comment, 	// content's attached comments
	tags: Content -> Tag,			// tags in the content
	references: Tag -> one users,		// tag reference to an user
}

abstract sig PrivacyLevel{}
one sig OnlyMe, Friends, FriendsOfFriends, Everyone extends PrivacyLevel{}


/////////////// PUBLISH and UNPUBLISH ///////////////
// publish a piece of content on a user’s wall. The content may be the existing one. 
pred publish [n, n' : Nicebook, u : User, c : Content,
			 viewPrivacy: PrivacyLevel, commentPrivacy: PrivacyLevel] {

	n'.users = n.users
	n'.friends = n.friends
	n'.walls = n.walls
	n'.comments = n.comments
	n'.tags = n.tags
	n'.references = n.references
	n'.wallPrivacy = n.wallPrivacy	

       //the user should be a registered user
	u in n.users
	//the content should not has been published by any user in the nicebook
	c not in n.users.(n.walls).(n.published)

	//if the content c is a new content
       c not in User.(n.own) 
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
			(c.(n.tags).(n.references).(n.walls) -> c)
}
assert publishPreserveInv {
	all n, n': Nicebook, u: User, c: Content,
		vPrivacy: PrivacyLevel, cPrivacy:  PrivacyLevel |
			invariants[n] and upload[n, n', u, c, vPrivacy, cPrivacy]
			implies invariants[n']
} //check publishPreserveInv

// hide a piece of content on a user’s wall
pred unpublish [n, n' : Nicebook, u : User, c : Content] {

	// only the owner can hide the content on his/her and related user's wall
	n'.users = n.users
	n'.friends = n.friends
	n'.own = n.own
	n'.walls = n.walls
	n'.comments = n.comments
	n'.tags = n.tags
	n'.references = n.references
	n'.wallPrivacy = n.wallPrivacy

       //the user should be a registered user
       u in n.users
       //the content should be owned by the user
	c in u.(n.own)
       //the content should has been published
       c in u.(n.walls).(n.published)

	n'.published = n.published - 
                            //remove the content from user self's wall
				(u.(n.walls) -> c) - 
                            //remove the content from all taged users' wall
				(c.(n.tags).(n.references).(n.walls) -> c)
}
assert unpublishPreserveInv {
	all n, n': Nicebook, u: User, c: Content |
		invariants[n] and unpublish[n, n', u, c]
		implies invariants[n']
} //check unpublishPreserveInv

/////////////// UPLOAD and REMOVE ///////////////
// Upload a piece of content, excluding the attacked comments
pred upload [n, n': Nicebook, u: User, c: Content, vPrivacy: PrivacyLevel, cPrivacy: PrivacyLevel] {
	// precondition
	// the content doesn't exist
	c not in n.own[User]

	// postcondition
	// the content belongs to the user
	n'.own = n.own + (u -> c)
	// set privacy of the content
	c.ViewPrivacy = vPrivacy
	c.CommentPrivacy = cPrivacy

	n'.users = n.users
	n'.friends = n.friends
	n'.walls = n.walls
	n'.published = n.published
	n'.wallPrivacy = n.wallPrivacy
	n'.comments = n.comments
	n'.tags = n.tags
	n'.references = n.references
}
assert uploadPreserveInv {
	all n, n': Nicebook, u: User, c: Content,
		vPrivacy: PrivacyLevel, cPrivacy:  PrivacyLevel |
			invariants[n] and upload[n, n', u, c, vPrivacy, cPrivacy]
			implies invariants[n']
} //check uploadPreserveInv

// Remove an existing piece of content from a user’s account.
pred remove [n, n': Nicebook, u: User, c: Content] {
	// precondition
	// the content must belong to the user
	c in n.own[u]

	// postcondition
	// remove the content form the user
	n'.own = n.own - (u -> c)
	// remove from owner's and tagged users' published
	n'.published = n.published - (n.walls[u + n.references[n.tags[c]]]  -> c)
	// remove the attached comments
	n'.comments = n.comments - (c -> n.comments[c])
	// TODO should attached comments do: remove[n.comments[c]]?
	// photos contained by the note should also be removed
	c in Note implies remove[n, n', u, c.contains]
	// remove tags of the content
	n'.tags = n.tags - (c -> n.tags[c])
	// remove references from tags
	n'.references = n.references - (n.tags[c] -> n.references[n.tags[c]])

	n'.users = n.users
	n'.friends = n.friends
	n'.walls = n.walls
	n'.wallPrivacy = n.wallPrivacy
}
assert removePreserveInv {
	all n, n': Nicebook, u: User, c: Content |
		invariants[n] and remove[n, n', u, c] implies invariants[n']
} //check removePreserveInv for 10


/////////////// ADD COMMENT ///////////////
// Add a comment to a content.
pred addComment [n, n': Nicebook, u: User, comment: Comment, content: Content] {
	// precondition
	// the comment doesn't exist
	comment not in n.comments[content]
	// authorized to add comment to the content
	content in commentable[n, u]

	// postcondition
	n'.comments = n.comments + (content -> comment)
	// the comment must belong to the user
	n'.own = n.own + (u -> comment)
	// the comment is attached to the content
	n'.comments = n.comments + (content -> comment)
	// set comment's privacy
	comment.ViewPrivacy = content.ViewPrivacy
	comment.CommentPrivacy = content.CommentPrivacy

	n'.users = n.users
	n'.friends = n.friends
	n'.walls = n.walls
	n'.published = n.published
	n'.wallPrivacy = n.wallPrivacy
	n'.tags = n.tags
	n'.references = n.references
}
assert addCommentPreserveInv {
	all n, n': Nicebook, u: User, c: Content , comment: Comment| 
		invariants[n] and addComment[n, n', u, comment, c] implies invariants[n']
} //check addCommentPreserveInv for 10

/////////////// ADD TAG & REMOVE TAG ///////////////
// add a tag to a note or photo
pred addTagInvariant [n, n' : Nicebook, u1, u2 : User, c : Content, t : Tag] {

	//u1 is the user who launched the "addTag" action
	//u2 is the user who is tagged by u1

	// precondition: 
	// user who tags another user must be that user's friend, i.e., 
	// u1 should be a friend of u2(tagged user)
	(u1 in n.friends[u2])
	// the content to be tagged must be published on some wall
	some (n.published).c
	// only photo and note can be tagged
	c not in Comment
	
	//postcondition:
	//content is added to the wall of user and tag is added to the content
	n'.published = n.published + (u2.(n.walls))->c
	n'.tags = n.tags + (c -> t)
	n'.references = n.references + (t -> u2)

	// nothing else changes 
	n'.users = n.users
	n'.friends = n.friends
	n'.own = n.own
	n'.walls = n.walls
	n'.comments = n.comments
	n'.wallPrivacy = n.wallPrivacy
}
assert addTagPreservesInvariant {
	all n, n' : Nicebook, u1,u2 : User, c : Content, t : Tag |
		invariants[n] and addTagInvariant[n, n', u1, u2, c, t] implies
			invariants[n']
} //check addTagPreservesInvariant for 7

// remove a tag on a note or photo
pred removeTagInvariant[n, n' : Nicebook, u : User, c : Content, t : Tag] {
	// precondition:
	// content c must be present in tagged user's wall 
	c in ((u.(n.walls)). (n.published))
	// content is removed from the wall of user and tag is removed from the content
	(u in n.(own.c)) or (u in (t.(n.references)))

	//postcondition:
	// tag can be removed by owner of the post or tagged person
	
	n'.published = n.published - (u.(n.walls))->c  
	n'.tags = n.tags - (c -> t) 
	n'.references = n.references - (t -> u)

	//nothing else changes 
	n'.users = n.users
	n'.friends = n.friends
	n'.own = n.own
	n'.walls = n.walls
	n'.comments = n.comments
	n'.wallPrivacy = n.wallPrivacy
}
assert removeTagPreservesInvariant {
	all n, n' : Nicebook, u : User, c : Content, t : Tag |
		invariants[n] and removeTagInvariant[n, n', u, c, t] implies
			invariants[n']
} //check removeTagPreservesInvariant for 7

/////////////// PRIVACY ///////////////
pred setContentPrivacy[n : Nicebook, u : User, c : Content, p : PrivacyLevel] {
	// precondition
	// only the content's owner can change its viewPrivacy
	(u -> c) in n.own
	// postcondition
	// TODO: should it be c' ?
	c.ViewPrivacy = p
}
assert setContentPrivacyPreservesInvariant {
	all n, n' : Nicebook, u : User, c : Content, p : PrivacyLevel |
		invariants[n] and setContentPrivacy[n, u, c, p] implies
			invariants[n']
} //check setContentPrivacyPreservesInvariant for 7

pred setCommentPrivacy[n : Nicebook, u : User, c : Content, p : PrivacyLevel] {
	// precondition
	// only the content's owner can change its commentPrivacy
	(u -> c) in n.own
	// postcondition
	// TODO: should it be c' ?
	c.CommentPrivacy = p
}
assert setCommentPrivacyPreservesInvariant {
	all n, n' : Nicebook, u : User, c : Content, p : PrivacyLevel |
		invariants[n] and setCommentPrivacy[n, u, c, p] implies
			invariants[n']
} //check setCommentPrivacyPreservesInvariant for 7

fun commentable [n : Nicebook, u : User] : set Content{
	// return the contents that the user can comment
	{ c : Content | (c.CommentPrivacy = OnlyMe and n.own.c = u) or
			     (c.CommentPrivacy = Friends and u in (n.friends[n.own.c] + n.own.c)) or
			     (c.CommentPrivacy = FriendsOfFriends and u in (n.friends[n.friends[n.own.c]] + n.friends[n.own.c] + n.own.c)) or
			     (c.CommentPrivacy = Everyone) }	
}
fun viewable [n : Nicebook, u: User] : set Content{
	// return the content that can be viewed by the user
	// TODO also the content unpublished but owned by the user?
	{ c : n.published[Wall] | (c.ViewPrivacy = OnlyMe and n.own.c = u) or
			     (c.ViewPrivacy = Friends and u in (n.friends[n.own.c] + n.own.c)) or
			     (c.ViewPrivacy = FriendsOfFriends and u in (n.friends[n.friends[n.own.c]] + n.friends[n.own.c] + n.own.c)) or
			     (c.ViewPrivacy = Everyone) }
}

pred publishInvariant[n : Nicebook] {
	// TODO it's weird that unpublished content but also owned by the user cannot see it
	all u : n.users | (n.own[u] - n.published[n.walls[u]]) not in viewable[n, u]
}

pred privacyWallContentInvariant[n : Nicebook, w : Wall, c : Content] {
	//the content privacy level is no lower than the wall privacy level
	n.wallPrivacy[w] = OnlyMe implies c.ViewPrivacy = OnlyMe and c.CommentPrivacy = OnlyMe
	n.wallPrivacy[w] = Friends implies c.ViewPrivacy in Friends + OnlyMe and c.CommentPrivacy in Friends + OnlyMe
	n.wallPrivacy[w] = FriendsOfFriends implies c.ViewPrivacy in (FriendsOfFriends + Friends + OnlyMe) and c.CommentPrivacy in (FriendsOfFriends + Friends + OnlyMe)
	n.wallPrivacy[w] = Everyone implies c.ViewPrivacy = PrivacyLevel and c.CommentPrivacy = PrivacyLevel
}
pred privacyInvariant[n : Nicebook] {
    	all c : Content | all u : User | (c.ViewPrivacy = OnlyMe and u != n.own.c implies c not in viewable[n, u]) and
						     (c.ViewPrivacy = Friends and u not in (n.own.c + n.friends[u]) implies c not in viewable[n, u]) and
						     (c.ViewPrivacy = FriendsOfFriends and u not in (n.own.c + n.friends[u] + n.friends[n.friends[u]]) implies c not in viewable[n, u])
}

assert NoPrivacyViolation {
	// violation occurs if a user is able to see content not in `viewable`
	all n : Nicebook | publishInvariant[n] and privacyInvariant[n]
} //check NoPrivacyViolation

/////////////// INVARIANTS ///////////////
pred contentInvariant [c: Content, n: Nicebook] {
	// the content belongs to only one user
	one u: n.users | c in n.own[u]
	// TODO must prevent circular
	c not in n.comments[c]
	// the note and its containing photos have same owner
	(c in Note and c.contains != none) implies (n.own.c = n.own.(c.contains))
}
pred wallInvariant[n : Nicebook] {
	//one n.walls.Wall // this may cause no instance found [TODO]
	// TODO attached comments should not be shown on owner's wall
	// the content published on someone's wall
	// should be owned by the user or be tagged
	all u: n.users | all c: n.published[n.walls[u]] |
		(c in n.own[u]) or (u in n.references[n.tags[c]])
}
pred userInvariant[n: Nicebook] {
	// a user cannot be his/her own friend
	all u : n.users | u not in n.friends[u]
	// if u1 is a friend of u2, then u2 is also a friend of u1
	all u1, u2 : n.users | (u1 != u2 and u2 in n.friends[u1]) implies u1 in n.friends[u2]
}
pred tagInvariant [n: Nicebook] {
	// the tag cannot be attached to comment
//	no t: Tag | t in n.tags[Comment] #[MODIFY]
//	no Comment.(n.tags)
}

pred invariants [n: Nicebook] {
	tagInvariant[n]
	wallInvariant[n]
	userInvariant[n]
	privacyInvariant[n]
	publishInvariant[n]

	all c: Content | contentInvariant[c, n]
	all w : Wall, c : Content | privacyWallContentInvariant[n, w, c]
}

run {
	all n: Nicebook | invariants[n]
} for 3 but exactly 1 Nicebook, exactly 2 User, exactly 5 Content
