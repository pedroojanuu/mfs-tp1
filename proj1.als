
--===============================================
-- M.EIC037: Formal Methods for Critical Systems
-- 2024/2025
--
-- Mini Project 1
--
-- Group Members:
--  Pedro Lima, 202108806
--  Pedro Januário, 202108768
--  Sofia Moura, 201907201
--
--===============================================

enum Status {External, Fresh, Active, Purged}

abstract sig Object {}

sig Message extends Object {
  var status: lone Status
}

sig Mailbox extends Object {
  var messages: set Message  
}

-- Mail application
one sig Mail {
  -- system mailboxes
  inbox: Mailbox,
  drafts: Mailbox,
  trash: Mailbox,
  sent: Mailbox,
  -- user mailboxes
  var uboxes: set Mailbox,

  var op: lone Operator -- added for tracking purposes only
}{
  no (inbox & drafts)
  no (inbox & trash)
  no (inbox & sent)
  no (drafts & trash)
  no (drafts & sent)
  no (trash & sent)
}

-- added for convenience, to track the operators applied during 
-- a system execution 
enum Operator {CMB, DMB, CM, GM, SM, DM, MM, ET}

-- Since we have only one Mail app, it is convenient to have
-- a global shorthand for its system mailboxes
fun sboxes : set Mailbox { Mail.inbox + Mail.drafts + Mail.trash + Mail.sent }

-- Returns the mailbox where a message is located
fun mailBoxOf[m: Message] : Mailbox {
  {mb: Mailbox | m in mb.messages}
}

------------------------------
-- Frame condition predicates
------------------------------

-- You can use these predicates in the definition of the operators

-- the status of the messages in M is unchanged from a state to the next
pred noStatusChange [M: set Message] {
  all m: M | m.status' = m.status
}

-- the set of messages in each mailbox in MB is unchanged from a state to the next
pred noMessageChange [MB: set Mailbox] {
  all mb: MB | mb.messages' = mb.messages
}

-- the set of user-defined mailboxes is unchanged from a state to the next
pred noUserboxChange {
  Mail.uboxes' = Mail.uboxes
}

-------------
-- Operators
-------------

/* Leave the constraint on Mail.op' in the operators.
   It is there to track the applied operators in each trace  
*/


/**
  * This predicate models the creation of a new message in the system.
  * Arguments:
  *   m: Message - The message to be created.
  */
pred createMessage [m: Message] {
  -- Preconditions
  m.status = Fresh

  -- Postconditions
  Mail.drafts.messages' = Mail.drafts.messages + m
  m.status' = Active
  Mail.op' = CM

  -- Frame conditions
  noStatusChange[Message - m]
  noMessageChange[Mailbox - Mail.drafts]
  noUserboxChange
}

-- moveMessage
pred moveMessage [m: Message, mb: Mailbox] {
  -- pre-conditions
  -- message should be active
  m.status = Active
  -- message should be in a mailbox
  some oldMb: Mailbox | m in oldMb.messages
  -- new mailbox must exist
  mb in (Mail.uboxes + sboxes - Mail.trash)
  -- new mailbox is not old mailbox
  all oldMb: Mailbox | m in oldMb.messages implies oldMb != mb
  
  -- post-conditions
  -- remove message from old mailbox
  all oldMb: Mailbox | m in oldMb.messages implies oldMb.messages' = oldMb.messages - m
  -- add message to new mailbox
  mb.messages' = mb.messages + m
  
  -- frame conditions
  noStatusChange[Message]
  noMessageChange[Mailbox - mb - mailBoxOf[m]]
  noUserboxChange

  Mail.op' = MM
}

-- deleteMessage
pred deleteMessage [m: Message] {
  -- pre-conditions
  -- message should be in a mailbox
  some oldMb: Mailbox | m in oldMb.messages
  -- message must not be deleted already
  m not in Mail.trash.messages
  
  -- post-conditions
  -- remove message from old mailbox
  all oldMb: Mailbox | m in oldMb.messages implies m not in oldMb.messages'
  -- add message to trash
  m in Mail.trash.messages'

  -- frame conditions
  noStatusChange[m]
  noMessageChange [Mailbox - Mail.trash]
  noUserboxChange

  Mail.op' = DM
}

/**
  * This predicate models sending a message from the drafts mailbox to the sent mailbox.
  * Arguments:
  *   m: Message - The message to be sent.
  */
pred sendMessage [m: Message] {
  -- Preconditions
  m in Mail.drafts.messages

  -- Postconditions
  Mail.drafts.messages' = Mail.drafts.messages - m
  Mail.sent.messages' = Mail.sent.messages + m
  Mail.op' = SM

  -- Frame conditions
  noStatusChange[Message]
  noMessageChange[Mailbox - (Mail.drafts + Mail.sent)]
  noUserboxChange
}

/**
  * This predicate models receiving an external message into the inbox.
  * Arguments:
  *   m: Message - The external message to be received.
  */
pred getMessage [m: Message] {
  -- Preconditions
  m.status = External

  -- Postconditions
  Mail.inbox.messages' = Mail.inbox.messages + m
  m.status' = Active
  Mail.op' = GM

  -- Frame conditions
  noStatusChange[Message - m]
  noMessageChange[Mailbox - Mail.inbox]
  noUserboxChange
}


/* Note:
   We assume that the spec implicitly means that the messages are not just
   marked as Purged but are also actually removed from the trash mailbox.
*/
-- emptyTrash
pred emptyTrash {
  -- pre-conditions
  -- trash is not empty
  some Mail.trash.messages
  
  -- post-conditions
  -- mark all messages in trash as purged
  all m: Message | m in Mail.trash.messages implies m.status' = Purged
  -- remove all messages in trash from system
  all m: Message | m in Mail.trash.messages implies m not in Object'
  -- trash is emptied
  Mail.trash.messages' = none
  
  -- frame conditions
  noStatusChange [Message - Mail.trash.messages]
  noMessageChange [Mailbox - Mail.trash]
  noUserboxChange

  Mail.op' = ET
}


-- createMailbox
pred createMailbox [mb: Mailbox] {
  -- pre-conditions
  mb not in Mail.uboxes
  mb not in sboxes
  no mb.messages

  -- post-conditions
  Mail.uboxes' = Mail.uboxes + mb
  Mail.op' = CMB

  -- frame
  noStatusChange[Message]
  noMessageChange[Mailbox]
}

-- deleteMailbox
pred deleteMailbox [mb: Mailbox] {
  -- pre-conditions
  mb in Mail.uboxes
  mb not in sboxes

  -- post-conditions
  Mail.uboxes' = Mail.uboxes - mb
  all msg : mb.messages | msg.status' = Purged
  Mail.op' = DMB
  mb.messages' = none

  -- frame
  noStatusChange[Message - mb.messages]
  noMessageChange[Mailbox - mb]
}

-- noOp
pred noOp {
  noStatusChange[Message]
  noMessageChange[Mailbox]
  noUserboxChange

  Mail.op' = none 
}

--------------------------
-- Inital state predicate
--------------------------

pred Init {
  -- There exist no active or purged messages anywhere
  no Message.status & Active
  no Message.status & Purged

  -- The system mailboxes are all distinct
  all mb1, mb2 : sboxes | mb1 != mb2 implies no mb1.messages & mb2.messages

  -- All mailboxes anywhere are empty
  all mb: Mailbox | no mb.messages

  -- The set of user-created mailboxes is empty
  no Mail.uboxes

  -- no operator generates the initial state
  Mail.op = none
}

------------------------
-- Transition predicate
------------------------

pred Trans {
  (some mb: Mailbox | createMailbox [mb])
  or
  (some mb: Mailbox | deleteMailbox [mb])
  or
  (some m: Message | createMessage [m])
  or  
  (some m: Message | getMessage [m])
  or
  (some m: Message | sendMessage [m])
  or   
  (some m: Message | deleteMessage [m])
  or 
  (some m: Message | some mb: Mailbox | moveMessage [m, mb])
  or 
  emptyTrash
  or 
  noOp
}


----------
-- Traces
----------

-- Restricts the set of traces to all and only the executions of the Mail app

fact System {
  -- traces must satisfy initial state condition and the transition condition
  Init and always Trans
}

--run {} for 10

---------------------
-- Sanity check runs
---------------------
pred p1 {
  -- Eventually a message becomes active
  eventually some m: Message | m.status = Active
}
//run p1 for 1 but 8 Object

pred p2 {
  -- The inbox contains more than one message at some point
  eventually #Mail.inbox.messages > 1
}
//run p2 for 1 but 8 Object

pred p3 {
  -- The trash mailbox eventually contains messages and
  -- becomes empty some time later
  eventually (some Mail.trash.messages and after eventually no Mail.trash.messages)
}
//run p3 for 1 but 8 Object

-- Eventually some message in the drafts mailbox (it is already there) moves to the sent mailbox
pred p4 {
  eventually some m: Message | m in Mail.drafts.messages and after (m in Mail.sent.messages)
}
//run p4 for 1 but 8 Object

-- Eventually there is a user mailbox with messages in it
pred p5 {
  eventually (some Mail.uboxes.messages)
}
//run p5 for 1 but 8 Object 

-- Eventually the inbox gets two messages in a row from outside
/*
 Note:
 We considered that "gets two messages in a row from outside" means the inbox receives
 a message from outside in one state and then receives another message from outside
 in the next state.
*/
pred p6 {
  eventually some m1: Message, m2: Message | 
    m1 != m2 and getMessage[m1] and after (getMessage[m2])
}
//run p6 for 1 but 8 Object

pred p7 {
  -- Eventually some user mailbox gets deleted
  eventually some m: Mailbox | m in Mail.uboxes and after m not in Mail.uboxes
}
//run p7 for 1 but 8 Object

pred p8 {
  -- Eventually the inbox has messages
  eventually some Mail.inbox.messages
  -- Every message in the inbox at any point is eventually removed 
  always all m: Message | m in Mail.inbox.messages implies eventually m not in Mail.inbox.messages
}
//run p8 for 1 but 8 Object

pred p9 {
  -- The trash mail box is emptied of its messages eventually
  eventually no Mail.trash.messages
}
//run p9 for 1 but 8 Object

pred p10 {
  -- Eventually an external message arrives and 
  -- after that nothing happens anymore
  eventually (some m: Message | m.status = External and after always noOp)
}
//run p10 for 1 but 8 Object



--------------------
-- Valid Properties
--------------------

assert v1 {
  -- Every active message is in one of the app's mailboxes 
  always (all m: Message | m.status = Active implies some mb: Mailbox | m in mb.messages)
}
//check v1 for 5 but 11 Object

 
assert v2 {
  -- Inactive messages are in no mailboxes at all
  always (all m: Message | m.status != Active implies no mb: Mailbox | m in mb.messages)
}
--check v2 for 5 but 11 Object

-- Each of the user-created mailboxes differs from the predefined mailboxes
assert v3 {
  always no (Mail.uboxes & sboxes)
}
--check v3 for 5 but 11 Object

-- Every active message was once external or fresh.
assert v4 {
  always all m: Message | m.status = Active implies once (m.status = Fresh or m.status = External)
}
--check v4 for 5 but 11 Object

-- Every user-created mailbox starts empty.
assert v5 {
  always all u: Mail.uboxes | once (historically no u.messages)
}
--check v5 for 5 but 11 Object

assert v6 {
-- User-created mailboxes stay in the system indefinitely or until they are deleted.
  always (all m: Mailbox | (m in Mail.uboxes) implies
      always (m in Mail.uboxes) or (m in Mail.uboxes until deleteMailbox[m]))
}
// check v6 for 5 but 11 Object

assert v7 {
-- Every sent message is sent from the draft mailbox 
  always (all m: Message | (m in Mail.sent.messages and sendMessage[m]) implies once (m in Mail.drafts.messages))
}
// check v7 for 5 but 11 Object

assert v8 {
-- The app's mailboxes contain only active messages
  always all m: Message | (some mb: Mailbox | m in mb.messages) => m.status = Active
}
--check v8 for 5 but 11 Object

assert v9 {
  -- Every received message passes through the inbox
  always (all m: Message | getMessage[m] implies after m in Mail.inbox.messages)
}
--check v9 for 5 but 11 Object

assert v10 {
  -- A purged message is purged forever
  always (all m: Message | m.status = Purged implies always m.status = Purged)
}
--check v10 for 5 but 11 Object

assert v11 {
  -- No messages in the system can ever (re)acquire External status
  always (all m: Message | m.status != External implies always m.status != External)
}
--check v11 for 5 but 11 Object

-- The trash mailbox starts empty and stays so until a message is deleted, if any
assert v12 {
  always (
     (no Mail.trash.messages until some m: Message | deleteMessage[m])
  )
  or
  always (no Mail.trash.messages)
}
check v12 for 5 but 11 Object

-- To purge an active message one must first delete the message 
-- or delete the mailbox it is in.
assert v13 {
  always (
    all m: Message | (
      once m.status = Active and m.status = Purged
    ) implies (
      once deleteMessage[m] 
      or 
      once deleteMailbox[mailBoxOf[m]]
    )
  )
}
--check v13 for 5 but 11 Object

-- Every message in the trash mailbox had been previously deleted
assert v14 {
  always (all m: Mail.trash.messages | (once deleteMessage[m]))
}
--check v14 for 5 but 11 Object

assert v15 {
-- Every message in a user-created mailbox ultimately comes from a system mailbox.

}
--check v15 for 5 but 11 Object

assert v16 {
-- A purged message that was never in the trash mailbox must have been 
-- in a user mailbox that was later deleted

}
--check v16 for 5 but 11 Object


----------------------
-- Invalid Properties
----------------------

-- It is possible for messages to stay in the inbox indefinitely
-- Negated into: it's not possible for a message to stay in the inbox indefinetely
assert i1 {
  all m: Message | always (m in Mail.inbox.messages implies eventually (m not in Mail.inbox.messages))
}
--check i1 for 5 but 11 Object

-- A message that was removed from the inbox may later reappear there.
-- Negated into: a message that was removed from the inbox must NEVER reappear there.
assert i2 {
  always (some m: Message | (historically m in Mail.inbox.messages and (deleteMessage[m] or moveMessage[m, sboxes - Mail.inbox])) implies always m not in Mail.inbox.messages)
}
--check i2 for 5 but 11 Object

-- A deleted message may go back to the mailbox it was deleted from.
-- Negated into:
-- A deleted message can never go back to the mailbox it was deleted from.

-- Note:
-- We considered a deleted message to be a message that is in the trash mailbox,
-- not a purged message.

-- Original assertion:
-- some m: Message | let box = mailBoxOf[m] | eventually (m in Mail.trash.messages and eventually (m in box.messages))
assert i3 {
  always (all m: Message | let box = mailBoxOf[m] | m in Mail.trash.messages implies always (m not in box.messages))
  or
  (always no Mail.trash.messages)
}
--check i3 for 5 but 11 Object

-- Some external messages may never be received
-- Negated into: all external message are eventually received
assert i4 {
  all m: Message | always (m.status = External implies eventually (m in Mail.inbox.messages))
}
--check i4 for 5 but 11 Object


