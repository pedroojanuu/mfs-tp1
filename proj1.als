
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
}

-- added for convenience, to track the operators applied during 
-- a system execution 
enum Operator {CMB, DMB, CM, GM, SM, DM, MM, ET}

-- Since we have only one Mail app, it is convenient to have
-- a global shorthand for its system mailboxes
fun sboxes : set Mailbox { Mail.inbox + Mail.drafts + Mail.trash + Mail.sent }

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


-- createMessage 
pred createMessage [m: Message] {


  Mail.op' = CM
}

-- moveMessage
pred moveMessage [m: Message, mb: Mailbox] {

  Mail.op' = MM
}


-- deleteMessage
pred deleteMessage [m: Message] {


  Mail.op' = DM
}

-- sendMessage
pred sendMessage [m: Message] {


  Mail.op' = SM
}

-- getMessage 
pred getMessage [m: Message] {


  Mail.op' = GM
}


/* Note:
   We assume that the spec implicitly means that the messages are not just
   marked as Purged but are also actually removed from the trash mailbox.
*/
-- emptyTrash
pred emptyTrash {


  Mail.op' = ET
}


-- createMailbox
pred createMailbox [mb: Mailbox] {


  Mail.op' = CMB
}

-- deleteMailbox
pred deleteMailbox [mb: Mailbox] {


  Mail.op' = DMB
}

-- noOp
pred noOp {


  Mail.op' = none 
}

--------------------------
-- Inital state predicate
--------------------------

pred Init {
  -- There exist no active or purged messages anywhere


  -- The system mailboxes are all distinct


  -- All mailboxes anywhere are empty


  -- The set of user-created mailboxes is empty


  -- [Keep this tracking constraint intact]
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


run {} for 10

---------------------
-- Sanity check runs
---------------------

pred p1 {
  -- Eventually a message becomes active

}
run p1 for 1 but 8 Object

pred p2 {
  -- The inbox contains more than one message at some point

}
run p2 for 1 but 8 Object

pred p3 {
  -- The trash mailbox eventually contains messages and
  -- becomes empty some time later

}
run p3 for 1 but 8 Object

pred p4 {
  -- Eventually some message in the drafts mailbox (it is already there) moves to the sent mailbox

}
run p4 for 1 but 8 Object

pred p5 {
  -- Eventually there is a user mailbox with messages in it

}
run p5 for 1 but 8 Object 

pred p6 {
  -- Eventually the inbox gets two messages in a row from outside

}
run p6 for 1 but 8 Object

pred p7 {
  -- Eventually some user mailbox gets deleted

}
run p7 for 1 but 8 Object

pred p8 {
  -- Eventually the inbox has messages

  -- Every message in the inbox at any point is eventually removed 

}
run p8 for 1 but 8 Object

pred p9 {
  -- The trash mail box is emptied of its messages eventually

}
run p9 for 1 but 8 Object

pred p10 {
  -- Eventually an external message arrives and 
  -- after that nothing happens anymore

}
run p10 for 1 but 8 Object



--------------------
-- Valid Properties
--------------------

assert v1 {
--  Every active message is in one of the app's mailboxes 

}
check v1 for 5 but 11 Object

 
assert v2 {
--  Inactive messages are in no mailboxes at all

}
check v2 for 5 but 11 Object

assert v3 {
-- Each of the user-created mailboxes differs from the predefined mailboxes

}
check v3 for 5 but 11 Object

assert v4 {
-- Every active message was once external or fresh.

}
check v4 for 5 but 11 Object

assert v5 {
-- Every user-created mailbox starts empty.

}
check v5 for 5 but 11 Object

assert v6 {
-- User-created mailboxes stay in the system indefinitely or until they are deleted.

}
check v6 for 5 but 11 Object

assert v7 {
-- Every sent message is sent from the draft mailbox 

}
check v7 for 5 but 11 Object

assert v8 {
-- The app's mailboxes contain only active messages

}
check v8 for 5 but 11 Object

assert v9 {
-- Every received message passes through the inbox

}
check v9 for 5 but 11 Object

assert v10 {
-- A purged message is purged forever

}
check v10 for 5 but 11 Object

assert v11 {
-- No messages in the system can ever (re)acquire External status

}
check v11 for 5 but 11 Object

assert v12 {
-- The trash mailbox starts empty and stays so until a message is deleted, if any

}
check v12 for 5 but 11 Object

assert v13 {
-- To purge an active message one must first delete the message 
-- or delete the mailbox it is in.

}
check v13 for 5 but 11 Object

assert v14 {
-- Every message in the trash mailbox had been previously deleted

}
check v14 for 5 but 11 Object

assert v15 {
-- Every message in a user-created mailbox ultimately comes from a system mailbox.

}
check v15 for 5 but 11 Object

assert v16 {
-- A purged message that was never in the trash mailbox must have been 
-- in a user mailbox that was later deleted

}
check v16 for 5 but 11 Object


----------------------
-- Invalid Properties
----------------------

-- It is possible for messages to stay in the inbox indefinitely
-- Negated into: 
assert i1 {

}
check i1 for 5 but 11 Object

-- A message that was removed from the inbox may later reappear there.
-- Negated into:
assert i2 {

}
check i2 for 5 but 11 Object

-- A deleted message may go back to the mailbox it was deleted from.
-- Negated into:
assert i3 {

}
check i3 for 5 but 11 Object

-- Some external messages may never be received
-- Negated into:
assert i4 {

}
check i4 for 5 but 11 Object


