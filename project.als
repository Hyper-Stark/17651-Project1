/*
 * Team Member 7:
 * 1) Jhao-Ting Chen
 * 2) Liwen Feng
 * 3) Rishabh Panwar
 * 4) Li Zhang
 */

// 1. structure of the social network, includes users and friendships
sig User {}
sig Wall {}

abstract sig PrivacyLevel{}
one sig OnlyMe, Friends, FriendsOfFriends, Everyone 
    extends PrivacyLevel{}

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
    // registered users
    users: set User,	
    // contents in Nicebook
    contents: set Content,

    // friends of a user
    friends: users -> users,
    // user's wall
    walls: users -> one Wall,
    // content uploaded by the user
    own: users -> contents,			

    // published content on the wall
    published: Wall -> contents,
    // wall's privacy level
    wallPrivacy: Wall -> one PrivacyLevel,	

    // content's attached comments
    comments: contents -> Comment, 	
    // tags in the content
    tags: contents -> users,			
}



pred userInScope [n: Nicebook, u: User] {
    u in n.users
}

pred contentInScope [n: Nicebook, c: Content] {
    c in n.contents
}

/////////////// PUBLISH and UNPUBLISH ///////////////
// publish a piece of content on a user’s wall.
// The content may be the existing one. 
pred publish [n, n' : Nicebook, u : User, c : Content,
			 viewPrivacy: PrivacyLevel,
			 commentPrivacy: PrivacyLevel] {
    n'.users = n.users
    n'.friends = n.friends
    n'.walls = n.walls
    n'.comments = n.comments
    n'.tags = n.tags
    n'.wallPrivacy = n.wallPrivacy
    //precondition
    c.ViewPrivacy = viewPrivacy
    c.CommentPrivacy = commentPrivacy

    //the user should be a registered user
    // the content should be in nicebook
    userInScope[n, u] and contentInScope[n, c]
    
    //the content should not has been 
    //published by any user in the nicebook
    c not in n.users.(n.walls).(n.published)
    
    //if the content c is a new content
    c not in n.contents
        implies 
            //we should upload it first
            n'.contents = n.contents  + c and
            //then update the relation between user to content
            n'.own = n.own + (u -> c)
        else
            //otherwise do not update the contents set
            n'.contents = n.contents
            //otherwise, c is an existing content, then do nothing
            n'.own = n.own


    n'.published = n.published + 
                //add the content to user self's wall
                (u.(n.walls) -> c) + 
                //add the content to all taged users' wall
                (n.walls[n.tags[c]] -> c)
}


assert publishPreserveInv {
    all n, n': Nicebook, 
        vPrivacy: PrivacyLevel, 
        cPrivacy:  PrivacyLevel |
    all u: n.users |
    all c: n.contents |
        invariants[n] and publish[n, n', u, c, vPrivacy, cPrivacy]
            implies 
        invariants[n']
} check publishPreserveInv for 10

// hide a piece of content on a user’s wall
pred unpublish [n, n' : Nicebook, u : User, c : Content] {

    // only the owner can hide the content
    // on his/her and related user's wall
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
    all n, n': Nicebook |
    all u: n.users |
    all c: n.contents |
    invariants[n] and unpublish[n, n', u, c] 
        implies 
    invariants[n']
} check unpublishPreserveInv for 10


/////////////// UPLOAD and REMOVE ///////////////
// Upload a piece of content, excluding the attached comments
pred upload [n, n': Nicebook, u: User, c: Content,
    vPrivacy: PrivacyLevel, cPrivacy: PrivacyLevel] {
    // precondition
    c.ViewPrivacy = vPrivacy
    c.CommentPrivacy = cPrivacy
    userInScope[n, u] and contentInScope[n, c]
    // the content doesn't exist
    c not in n.own[n.users]
    
    // postcondition
    // the content belongs to the user
    n'.own = n.own + (u -> c)
    n'.contents = n.contents + c
    
    //anything else should not be changed
    n'.users = n.users
    n'.friends = n.friends
    n'.walls = n.walls
    n'.published = n.published
    n'.wallPrivacy = n.wallPrivacy
    n'.comments = n.comments
    n'.tags = n.tags
}

assert uploadPreserveInv {
    all n, n': Nicebook, 
        vPrivacy: PrivacyLevel, 
        cPrivacy:  PrivacyLevel |
    all u: n.users | 
    all c: n.contents |
        invariants[n] and upload[n, n', u, c, vPrivacy, cPrivacy]
            implies
        invariants[n']
} check uploadPreserveInv for 10

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
    	(c in content.contains) implies
    	(content'.contains = content.contains - c)
    
    n'.users = n.users
    n'.friends = n.friends
    n'.walls = n.walls
    n'.wallPrivacy = n.wallPrivacy
}
assert removePreserveInv {
    all n, n': Nicebook |
    all u: n.users | 
    all c: n.contents |
    invariants[n] and remove[n, n', u, c] 
        implies 
    invariants[n']
} check removePreserveInv for 10

/////////////// ADD COMMENT ///////////////
// Add a comment to a content.
pred addComment [n, n': Nicebook, u: User, 
                comment: Comment, content: Content] {
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
    
    //anything else should not be changed
    n'.users = n.users
    n'.friends = n.friends
    n'.walls = n.walls
    n'.published = n.published
    n'.wallPrivacy = n.wallPrivacy
    n'.tags = n.tags
}



assert addCommentPreserveInv {
    all n, n': Nicebook | 
    all u: n.users | 
    all c: n.contents |
    all comment: n.contents |
    invariants[n] and 
    (comment in Comment) and 
    addComment[n, n', u, comment, c]
        implies 
    invariants[n']
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
    contentInScope[n, c]
    // user who tags another user must be that user's friend, i.e., 
    // u1 should be a friend of u2(tagged user)
    // also that user cannot be tagged by himself
    // as user cannot be his own friend
    (u1 in n.friends[u2])
    // the content to be tagged must be published on some wall
    some (n.published).c
    // only photo and note can be tagged
    c not in Comment
    
    // postcondition:
    // content is added to the wall of user and  
    // tag is added to the content
    n'.published = n.published + u2.(n.walls)->c
    n'.tags = n.tags + (c -> u2)
    
    // nothing else changes 
    n'.users = n.users
    n'.contents = n.contents
    n'.friends = n.friends
    n'.own = n.own
    n'.walls = n.walls
    n'.comments = n.comments
    n'.wallPrivacy = n.wallPrivacy
}
assert addTagPreservesInvariant {
    all n, n' : Nicebook |
    all u1, u2: n.users | 
    all c: n.contents |
    invariants[n] and addTag[n, n', u1, u2, c] 
        implies
    invariants[n']
} check addTagPreservesInvariant for 10

// remove a tag on a note or photo
pred removeTag[n, n' : Nicebook, u : User, c : Content] {
    // precondition:
    // user u is a user in nicebook n and so is content
    userInScope[n, u] and contentInScope[n, c]
    // content c must be present in tagged user's wall 
    c in (u.(n.walls)).(n.published)
    // user (who removes tag) can either be the owner of
    // that post or tagged to that post
    (c in n.own[u]) or (u in n.tags[c])
    
    // postcondition:
    // content is removed from the wall of user
    n'.published = n.published - (u.(n.walls))->c
    // tag is removed from the content
    n'.tags = n.tags - (c -> u)
    
    //nothing else changes 
    n'.users = n.users
    n'.contents = n.contents
    n'.friends = n.friends
    n'.own = n.own
    n'.walls = n.walls
    n'.comments = n.comments
    n'.wallPrivacy = n.wallPrivacy
}

assert removeTagPreservesInvariant {
    all n, n' : Nicebook |
    all u: n.users | 
    all c: n.contents |
    invariants[n] and removeTag[n, n', u, c]
        implies 
    invariants[n']
} check removeTagPreservesInvariant for 10

/////////////// PRIVACY ///////////////
pred setContentPrivacy[n, n' : Nicebook, u : User,
                        c, c' : Content, p : PrivacyLevel] {
    // precondition
    userInScope[n, u] and contentInScope[n, c]
    // only the content's owner can change its viewPrivacy
    (u -> c) in n.own
    // postcondition
    c'.ViewPrivacy = p
    // Update the content in Nicebook
    n'.own = n.own - u -> c + u -> c'
    
    //anything else should not be changed
    n'.users = n.users
    n'.contents = n.contents
    n'.friends = n.friends
    n'.walls = n.walls
    n'.own = n.own
    n'.published = n.published
    n'.wallPrivacy = n.wallPrivacy
    n'.comments = n.comments
    n'.tags = n.tags
}

assert setContentPrivacyPreservesInvariant {
    all n, n' : Nicebook, p : PrivacyLevel |
    all u: n.users | all c: n.contents | 
    all c': n'.contents |
    invariants[n] and 
    setContentPrivacy[n, n', u, c, c', p] 
        implies
    invariants[n']
} check setContentPrivacyPreservesInvariant for 10

pred setCommentPrivacy[n, n' : Nicebook, u : User,
                        c, c' : Content, p : PrivacyLevel] {
    // precondition
    userInScope[n, u] and contentInScope[n, c]
    // only the content's owner can change its commentPrivacy
    (u -> c) in n.own
    // postcondition
    c'.CommentPrivacy = p
    // Update the content in Nicebook
    n'.own = n.own - u -> c + u -> c'
    
    //anything else should not be changed
    n'.users = n.users
    n'.contents = n.contents
    n'.friends = n.friends
    n'.walls = n.walls
    n'.own = n.own
    n'.published = n.published
    n'.wallPrivacy = n.wallPrivacy
    n'.comments = n.comments
    n'.tags = n.tags
}

assert setCommentPrivacyPreservesInvariant {
    all n, n' : Nicebook, p : PrivacyLevel |
    all u: n.users | all c: n.contents | 
    all c': n'.contents |invariants[n] and
    setCommentPrivacy[n, n', u, c, c', p]
    	implies 
    invariants[n']
} check setCommentPrivacyPreservesInvariant for 10

fun commentable [n : Nicebook, u : User] : set Content{
    // return the contents that the user can comment
    { 
        c : n.contents | userInScope[n, u] 
            and 
        (
            // Only the owner can view the OnlyMe content.
            (
                c.CommentPrivacy = OnlyMe and 
                n.own.c = u
            ) 
                or
            // The owner can comment the Friends content 
            // and owner's friends can comment the published
            // Friends content.
            (
                c.CommentPrivacy = Friends and
                u in (n.friends[n.own.c] + n.own.c) and
                c in n.published[Wall]
            ) 
                or
            // The owner can comment the FriendsOfFriends 
            // content. And owner's friends and friends of 
            // owner's friends can comment the published
            // FriendsOfFriends content.
            (
                c.CommentPrivacy = FriendsOfFriends and
                u in (n.friends[n.friends[n.own.c]] +
                    n.friends[n.own.c] + n.own.c) and
                c in n.published[Wall]
            ) 
                or
            // Everyone can comment the Everyone content
            // which is published.
            (
                c.CommentPrivacy = Everyone and 
                c in n.published[Wall]
            )
    	) 
    }
}

fun viewable [n : Nicebook, u: User] : set Content{
    // return the content that can be viewed by the user
    { 
        c : n.contents | userInScope[n, u] 
        and 
        (
            // Only the owner can view the OnlyMe content.
            (
                c.ViewPrivacy = OnlyMe and
                n.own.c = u
            ) 
                or
            // The owner can view the Friends content 
            // and owner's friends can view the published
            // Friends content.
            (
                c.ViewPrivacy = Friends and 
                u in (n.friends[n.own.c] + n.own.c) and 
                c in n.published[Wall]
            )
                or
            // The owner can view the FriendsOfFriends 
            // content. And owner's friends and friends of 
            // owner's friends can view the published
            // FriendsOfFriends content.
            (
                c.ViewPrivacy = FriendsOfFriends and
                u in (n.friends[n.friends[n.own.c]] + 
                     n.friends[n.own.c] + n.own.c) and 
                c in n.published[Wall]
            )
                or
            // Everyone can view the Everyone content
            // which is published.
            (
                c.ViewPrivacy = Everyone and 
                c in n.published[Wall]
            )
        ) 
    }
}

pred publishInvariant[n : Nicebook] {
    // If the owner does not publish the content, then
    // the content can not view by anyone except the owner.
    all u : n.users | 
    all c : n.contents | 
    (c not in n.published[Wall] and u not in n.own.c) 
        implies 
    c not in viewable[n, u]
}

pred privacyWallContentInvariant[n : Nicebook, w : Wall, c : Content] {
    //the content privacy level is no lower 
    //than the wall privacy level
    
    //OnlyMe means the note can only be viewed by the owner.
    n.wallPrivacy[w] = OnlyMe 
        implies
    (
        c.ViewPrivacy = OnlyMe and 
        c.CommentPrivacy = OnlyMe
    )
    
    //Friends means the note can be viewed by the owner and his/her friends.
    n.wallPrivacy[w] = Friends 
        implies
    (
        c.ViewPrivacy in (Friends + OnlyMe) and
        c.CommentPrivacy in (Friends + OnlyMe)
    )
    
    //Friends means the note can be viewed by 
    //the owner, his/her friends, and the friends of his/her friends
    n.wallPrivacy[w] = FriendsOfFriends 
        implies
    (
        c.ViewPrivacy in (FriendsOfFriends + Friends + OnlyMe) and
        c.CommentPrivacy in (FriendsOfFriends + Friends + OnlyMe)
    )
    
    //Everyone means the note can be viewed by anyone
    n.wallPrivacy[w] = Everyone 
        implies
    (
        c.ViewPrivacy = PrivacyLevel and
        c.CommentPrivacy = PrivacyLevel
    )
}

pred ViewPrivacyInvariant[n : Nicebook] {
    // Users can not view the contents without adhering to 
    // the privacy rules
    all c : n.contents |
    all u : n.users |
    // If user is not the owner, the OnlyMe content is not 
    // viewable to the user.
    (
        c.ViewPrivacy = OnlyMe and u != n.own.c 
            implies
        c not in viewable[n, u]
    ) 
        and
    // If user is not the owner or the owner's friend, 
    // the Friends content is not viewable to the user.
    (
        c.ViewPrivacy = Friends and
        u not in (n.own.c + n.friends[u]) 
            implies
        c not in viewable[n, u]
    )
        and
    // If user is not the owner or the owner's friend or
    // the friend of the owner's friends, the 
    // FriendsOfFriends content is not viewable to the user.
    (
        c.ViewPrivacy = FriendsOfFriends and
        u not in (n.own.c + n.friends[u] +
        n.friends[n.friends[u]]) 
            implies
        c not in viewable[n, u]
    )
}

pred CommentPrivacyInvariant[n : Nicebook] {
    // Users can not comment the contents without adhering to 
    // the privacy rules
    all c : n.contents | 
    all u : n.users |
    // If user is not the owner, the OnlyMe content is not 
    // commentable to the user.
    (
        c.CommentPrivacy = OnlyMe and u != n.own.c 
            implies 
        c not in commentable[n, u]
    ) 
        and 
    // If user is not the owner or the owner's friend, 
    // the Friends content is not commentable to the user.
    (
        c.CommentPrivacy = Friends and u not in (n.own.c + n.friends[u])
            implies 
        c not in commentable[n, u]
    ) 
        and
    // If user is not the owner or the owner's friend or
    // the friend of the owner's friends, the 
    // FriendsOfFriends content is not commentable to the user.
    (
        c.CommentPrivacy = FriendsOfFriends and 
        u not in (n.own.c + n.friends[u] +
        n.friends[n.friends[u]])
            implies
        c not in commentable[n, u]
    )
}

/////////////// INVARIANTS ///////////////
pred contentInvariant [c: Content, n: Nicebook] {
    // the content belongs to only one user
    one u: n.users | c in n.own[u]
    // preventing comment circularity
    c not in c.^(n.comments)
    // the note and its containing photos have same owner
    (c in Note and c.contains != none) 
    implies (n.own.c = n.own.(c.contains))
    // an attached comment can only be attached to 1 content
    (c in n.comments[n.contents]) implies (one n.comments.c)
}

pred wallInvariant[n : Nicebook] {

    // every user has a wall
    all u: n.users | one n.walls[u]
    // different users have different walls
    all u1, u2: n.users | (u1 != u2) iff (n.walls[u1] != n.walls[u2])
    
    // attached comments should not be shown on owner's wall
    all c : n.contents, u : n.users |
    (c in Comment) and
    ((u in (n.own).c) and 
    (c not in ((n.own[u]).(n.comments))))
    	implies
    c not in n.published[n.walls[u]]
    
    // the content published on someone's wall
    // should be owned by the user or be tagged
    all u: n.users | 
    all c: n.published[n.walls[u]] |
    (c in n.own[u]) or (u in n.tags[c])
}

pred userInvariant[n: Nicebook] {
    // a user cannot be his/her own friend
    all u : n.users | u not in n.friends[u]
    // if u1 is a friend of u2, then u2 is also a friend of u1
    all u1, u2 : n.users |
    (u1 != u2 and u2 in n.friends[u1]) 
        implies 
    u1 in n.friends[u2]
}

pred tagInvariant [n: Nicebook] {
    // the tag cannot be attached to comment
    no u: n.users | u in n.tags[Comment]
}

//list of all invariants that need to be preserved
pred invariants [n: Nicebook] {

    publishInvariant[n]
    
    all w : Wall, c : n.contents | 
        privacyWallContentInvariant[n, w, c]
    ViewPrivacyInvariant[n]
    CommentPrivacyInvariant[n]
    
    all c: n.contents | contentInvariant[c, n]
    wallInvariant[n]
    userInvariant[n]
    tagInvariant[n]
}

//run command of each operation
run publish
run unpublish
run upload
run remove
run addComment
run addTag
run removeTag
run setContentPrivacy
run setCommentPrivacy

run {
    all n: Nicebook | invariants[n]
} for 10
