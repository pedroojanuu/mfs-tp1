
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

enum Status {External, Fresh, Active, Purged, Scheduled}

abstract sig Object {}

sig Message extends Object {
  var status: lone Status,
  var timeToSend: lone Int
}{
  some timeToSend <=> status = Scheduled
  timeToSend >= 0
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
  scheduled: Mailbox,
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
  no (inbox & scheduled)
  no (drafts & scheduled)
  no (trash & scheduled)
  no (sent & scheduled)
}

-- added for convenience, to track the operators applied during 
-- a system execution 
enum Operator {CMB, DMB, CM, GM, SM, DM, MM, ET, SCM}

-- Since we have only one Mail app, it is convenient to have
-- a global shorthand for its system mailboxes
fun sboxes : set Mailbox { Mail.inbox + Mail.drafts + Mail.trash + Mail.sent + Mail.scheduled }

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
  m.status = External

  -- Postconditions
  Mail.drafts.messages' = Mail.drafts.messages + m
  m.status' = Fresh
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
  mb in (Mail.uboxes + sboxes)
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
  m.status = Fresh
  m in Mail.drafts.messages

  -- Postconditions
  m.status' = Active
  Mail.drafts.messages' = Mail.drafts.messages - m
  Mail.sent.messages' = Mail.sent.messages + m
  Mail.op' = SM

  -- Frame conditions
  noStatusChange[Message - m]
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

  -- frame
  noStatusChange[Message - mb.messages]
  noMessageChange[Mailbox]
}

pred scheduleMessage[m: Message, t: Int] {
  -- pre-conditions
  m.status = Fresh
  m in Mail.drafts.messages
  t > 0
  no m.timeToSend
  
  -- post-conditions
  m.status' = Scheduled
  m.timeToSend' = t
  Mail.drafts.messages' = Mail.drafts.messages - m
  Mail.scheduled.messages' = Mail.scheduled.messages + m
  Mail.op' = SCM

  -- frame conditions
  noStatusChange[Message - m]
  noMessageChange[Mailbox - (Mail.drafts + Mail.scheduled)]
  noUserboxChange
}

pred updateSchedule[m: Message] {
  -- pre-conditions
  m.status = Scheduled

  -- post-conditions
  m.timeToSend = 0 implies sendScheduled[m]
  m.timeToSend > 0 implies m.timeToSend' = sub[m.timeToSend, 1]

  -- no frame conditions, because this operation should
  -- happen at the same time as other operators
}

pred sendScheduled[m: Message] {
  -- pre-conditions
  m.status = Scheduled
  m.timeToSend = 0

  -- post-conditions
  m.status' = Active
  m.timeToSend' = none
  Mail.scheduled.messages' = Mail.scheduled.messages - m
  Mail.sent.messages' = Mail.sent.messages + m
  Mail.op' = SM

  -- frame conditions
  noStatusChange[Message - m]
  noMessageChange[Mailbox - (Mail.scheduled + Mail.sent)]
  // noStatusChange[Message]
  // noMessageChange[Mailbox]
  noUserboxChange
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
  -- ?????????????????
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
  (
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
    (some m: Message | some t: Int | t > 0 and scheduleMessage [m, t])
    or
    (some m: Message | sendScheduled [m])
    or 
    noOp
  ) and (
    -- update the time and status of all schedule messages in the system
    all m: Message | m.status = Scheduled implies updateSchedule[m]
  )
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

-------------------
-- New Facts to Improve the Model
-------------------

-- The system starts with all messages being either Fresh or External
fact startFreshOrExternal {
  all m: Message | m.status = External or no m.status
}

-- This fact guarantees that the messages in the drafts mailbox are only Fresh
fact onlyFreshInDrafts {
  always (all m: Mail.drafts.messages | m.status = Fresh)
}

fact onlyScheduledInScheduled {
  always (all m: Mail.scheduled.messages | m.status = Scheduled)
}

fact noScheduledOutsideScheduled {
  always (all m: Message | m.status = Scheduled implies m in Mail.scheduled.messages)
}

-- This fact guarantees that the messages in the inbox were once received
-- this does not mean that the messages in the inbox cannot be moved,
-- but that we can only move messages to the inbox, that were once there
fact onlyReceivedInInbox {
  always (all m: Mail.inbox.messages | once getMessage[m])
}

-- The same for sent mailbox
fact onlySentInSent {
  always (all m: Mail.sent.messages | once (sendMessage[m] or sendScheduled[m]))
}

---------------------
-- Sanity check runs
---------------------

-- Eventually there should at least one scheduled message
pred p1 {
  eventually(some m: Message | m.status = Scheduled)
}
//run p1 for 5 but 11 Object

-- Eventually some message is sent without never being scheduled
pred p1a {
  eventually(some m: Message | sendMessage[m])
}
//run p1a for 5 but 11 Object

-- Eventually some message should be scheduled and between it being secheduled and sent another message should be created
pred p2 {
  eventually(some m: Message | m.status = Scheduled and some m: Message | createMessage[m])
}
//run p2 for 5 but 11 Object

-- Eventually there should be 2 scheduled messages at the same time
pred p3 {
  eventually(#({m: Message | m.status = Scheduled}) = 2)
}
//run p3 for 5 but 11 Object

-- Eventually a user-created mailbox gets created, filled, then deleted.
pred p4 {
  some u: Mailbox |
    eventually (
      u in Mail.uboxes and
      some m: Message | m in u.messages and
      eventually (u not in Mail.uboxes)
    )
}
//run p4 for 1 but 8 Object

-- A message is created, sent, then deleted, then purged.
-- Note: we considered that a message is deleted when it is moved to the trash, 
-- not when it is purged.
pred p5 {
  some m: Message |
    eventually (
      m.status = Fresh and
      eventually (m.status = Active and m in Mail.sent.messages and
      eventually (m in Mail.trash.messages and
      eventually (m.status = Purged)))
    )
}
//run p5 for 1 but 8 Object

-- Eventually some message is moved into the inbox
pred p6 {
  eventually (some m: Message | moveMessage[m, Mail.inbox])
}
//run p6 for 5 but 11 Object

-- Eventually some message is moved into the sent mailbox
pred p7 {
  eventually (some m: Message | moveMessage[m, Mail.sent])
}
//run p7 for 5 but 11 Object

-- Eventually, all mailbox contain exactly 1 message
pred p8 {
  eventually (all mb: Mailbox | #(mb.messages) = 1)
}
//run p8 for 5 but 11 Object

--------------------
-- Valid Properties
--------------------

-- Every scheduled message should eventually be sent
assert v1 {
  always (all m: Message | m.status = Scheduled implies eventually (m in Mail.sent.messages))
}
//check v1 for 5 but 11 Object

-- No message can be in two mailboxes at the same time.
assert v2 {
  always (all mb1, mb2: Mailbox | mb1 != mb2 implies no mb1.messages & mb2.messages)
}
check v2 for 5 but 11 Object

-- Once active, a message can never return to the drafts mailbox
assert v3{
  always (all m: Message | m.status = Active implies always m not in Mail.drafts.messages)
}
//check v3 for 5 but 11 Object

-- No message can be in 2 states at the same time
assert v4 {
  always (all m: Message | #(m.status) <= 1)
}
//check v4 for 5 but 11 Object

-- All messages moved into the inbox mailbox where once there
assert v5 {
  always (all m: Message | moveMessage[m, Mail.inbox] implies once m in Mail.inbox.messages)
}
//check v5b for 5 but 11 Object

-- All messages moved into the sent mailbox where once there
assert v6 {
  always (all m: Message | moveMessage[m, Mail.sent] implies once m in Mail.sent.messages)
}
//check v6b for 5 but 11 Object

-- All messages in the drafts mailbox where once created
assert v7 {
  all m: Mail.drafts.messages | once createMessage[m]
}
//check v7 for 5 but 11 Object

-- All messages without mailbox should be External
assert v8 {
  always (all m: Message | no mailBoxOf[m] implies m.status = External)
}
// check v8 for 5 but 11 Object

-- No messages from the inbox can end up in sent and vice-versa
assert v9 {
  always (all m: Message | m in Mail.inbox.messages implies m not in Mail.sent.messages)
  always (all m: Message | m in Mail.sent.messages implies m not in Mail.inbox.messages)
}
//check v9 for 5 but 11 Object

----------------------
-- Invalid Properties
----------------------

-- It can exist multiple scheduled messages at the same time
-- Negation: It can never exist multiple scheduled messages at the same time
assert i1 {
  always (some m1, m2: Message | m1 != m2 implies m1.status = Scheduled and m2.status = Scheduled)
}
//check i1 for 5 but 11 Object

-- A message can move from one user-created mailbox to another
-- Negation: A message can never be moved from one user-created mailbox to another
assert i2 {
  always all m: Message, u1, u2: Mail.uboxes |
    u1 != u2 implies
    (m in u1.messages implies always m not in u2.messages)
}
//check i2 for 5 but 11 Object

