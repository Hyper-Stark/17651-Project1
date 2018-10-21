// 1. structure of the social network, includes users and friendships
sig User {
	friends: User,
	has : one Wall
}
abstract sig Content {
	ownedBy: one User,
	ViewPrivacy: one PrivacyLevel,
       CommentPrivacy: one PrivacyLevel
}
sig Note extends Content {
	contains : some Photo
	associatedWith : some Tag
}
sig Photo extends Content {
	associatedWith : some Tag
}
sig Comment extends Content {
	attachedTo: one Content
}

sig Tag {
	// reference to only one user
	// can only be added to photo or note
	reference: one User
}

sig Wall {
	// belongs to a user
	// have many notes and photos
	published : Content,
	privacySetting: one PrivacyLevel
}

sig Nicebook {

}
abstract sig PrivacyLevel{}

one sig OnlyMe, Friends, FriendsOfFriends, Everyone extends PrivacyLevel{}

// Upload a piece of content
pred upload [u: User, c: Content] {
	// precondition
	// the content doesn't exist

	// postcondition
	// the content belongs to the user
	// the privacy level is Everyone
}

// Remove an existing piece of content from a user’s account.
pred remove [u: User, c: Content] {
	// precondition
	// the content must belong to the user

	// postcondition
	// remove the attached comments
	// remove the tags
	// remove the content form the user
}

// Add a comment to a content.
pred addComment [u: User, c: Comment, content: Content] {
	// precondition
	// the comment doesn't exist
	// authorized to add comment to the content

	// postcondition
	// the comment must belong to the user
	// the comment is attached to the content
}
run{}for 3 but exactly 5 Content


/*abstract sig PrivacyLevel {}
one OnlyMe, Friends, FriendsOfFriends, Everyone extends PrivacyLevel {}

// 2. operations for modifying user content

// upload a piece of content, photo, comment, or note
pred upload [] {
// only the owner or owner’s friends can post notes or photos
}

// publish a piece of content on a user’s wall. The content may be the existing one. 
pred publish [] {
	// only the owner can publish the content on his/her wall
}

// hide a piece of content on a user’s wall
pred unpublish [] {
	// only the owner can hide the content on his/her wall
}

// add a comment to an existing photo, note, or another comment
pred addComment [] {
	// only viewable content to a user can be added comment
}


// add a tag to a note or photo
pred addTag [] {
	// the content should publish on the wall of the tagged user
}

// remove a tag on a note or photo
pref removeTag[] {
}

pred removeTag [] {}


// 3. Privacy setting that control access to those content

fun viewable [u: User] {
	// return the content that can be viewed by the user
}

assert NoPrivacyViolation {
	// violation occurs if a user is able to see content not in `viewable`
}*/

pred invariants{
	// if u1 is a friend of u2, then u2 is also a friend of u1
	all u1,u2 : User | u1 != u2 and u1 in u2.friends implies u2 in u1.friends
	// users and content are belongs to only one social network
	
	// user can only add comments to content the user owns or viewable to the user (`viewable`)
        all c : Content | one (Content.ownedBy)
}
