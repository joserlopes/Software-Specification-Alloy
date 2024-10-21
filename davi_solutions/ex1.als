sig Node {
    outbox: set Msg // set of messages to redirect
}

sig Member in Node {
    nxt: one Member, // next member
    qnxt: Node -> lone Node, // node -> next in queue for membership
}

one sig Leader in Member {
    lnxt: Node -> lone Node // leader -> leader queue
}

sig LQueue in Member {} // set of nodes in leader queue

abstract sig Msg {
    sndr: Node, // Sender node
    rcvrs: set Node // Nodes messages was delivered
}

sig SentMsg, SendingMsg, PendingMsg in Msg {}

/*
    1. Forming the loop
*/

// 1.1 All members must have a nxt and be the nxt of someone
fact {
    Member = nxt.Member
    &&
    Member = Member.nxt
}

// 1.2 next cannot be reciprocal
fact {
    no (nxt & ~nxt)
}

// 1.3 Every member can reach every other one through nxt (loops)
fact {
    all m1, m2: Member |
        m1 in (m2.^nxt) && m2 in (m1.^nxt)
}

/*
    2. Membership queue
*/

// 2.1 No members in domain of Member.qnxt
fact {
    all m: Member |
        no (Member & m.qnxt.Node) 
}

// 2.2 Owner of the queue must appear once in its co-domain if the list is not empty
fact {
    all m: Member |
        some m.qnxt 
        implies
        (Member & Node.(m.qnxt)) = m
}

// 2.3 Nodes can only queue once
fact {
    all m: Member, n: Node |
        n !in (n.^(m.qnxt))
}

// 2.4 Each node is 'pointed to' only once (including owner)
fact {
    all m:Member, n1:Node |
        lone n2: Node | n1 in n2.(m.qnxt)
}

// 2.5 Each node in the queue can eventually reach the owner
fact {
    all m: Member |
        all n: Node |
            n in m.qnxt.Node 
            implies
            m in n.^(m.qnxt)
}

// 2.6 Non-member nodes can only appear in the queue of one member
fact {
    all n: Node - Member |
        lone m: Member | n in m.qnxt.Node
}


fun visualizeMemberQueues[]: Node->Node {
    Member.qnxt
}


/*
    3. Leadership queue
*/


// 3.1 LQueue has all members in Leaders queue
fact {
    all m: Member |
        m in Leader.lnxt.Node
        implies
        m in LQueue
}

// 3.2 Leader is not in LQueue
fact {
    Leader !in LQueue
}

// 3.3 No non-members or leader in domain of Leader.lnxt
fact {
    no (((Node-Member)+Leader) & Leader.lnxt.Node)
}

// 3.4 No non-members in the codomain of Leader.lnxt
fact {
    no ((Node-Member) & Node.(Leader.lnxt)) 
}

// 3.5 Owner of the queue must appear once in its co-domain if the list is not empty
fact {
    some Leader.lnxt 
        implies
    (Leader in Node.(Leader.lnxt))
}

// 3.6 Each member can only queue once 
fact {
    all m:Member |
        m in Leader.lnxt.Node
        implies
        one m & Leader.lnxt.Node
}

// 3.7 Each node is 'pointed to' only once (including owner)
fact {
    all m1:Member |
        lone m2: Node | m1 in m2.(Leader.lnxt)
}

// 3.8 Each node in the queue can eventually reach the leader
fact {
    all m: Member |
        m in Leader.lnxt.Node
        implies
        Leader in m.^(Leader.lnxt)
}

fun visualizeLeaderQueues[]: Node->Node {
    Leader.lnxt
}


/*
    4. Message status consistency
*/ 

// 4.0 redundant: no messages without status
fact {
    all m:Msg |
    m in SentMsg 
    || m in SendingMsg
    || m in PendingMsg
}

// 4.1 Sent, Sending and Pending are disjoint
fact {
    disj[SentMsg, SendingMsg, PendingMsg]
}

// 4.2 There can be one or zero sending message at a time
fact {
    lone SendingMsg
}

// 4.3 Sending messages have the current Leader as the sender
fact {
    some SendingMsg
    implies
    SendingMsg.sndr = Leader
}

// 4.4 Sending Messages need to have at least some receiver
fact {
    some SendingMsg
    implies
    some SendingMsg.rcvrs
}

// 4.5 Sending Messages need to be in one member's outbox
fact {
    some SendingMsg
    implies
    SendingMsg in Node.outbox
}

// 4.6 Outbox contains no sent messages
fact {
    no Node.outbox & SentMsg
}

// 4.7 Outbox contains all pending messages of the current node
fact {
    all n: Node |
        (sndr.n & PendingMsg) in n.outbox
}

// 4.8 If node has a Sending message in its outbox, node is a member
fact {
    all n: Node |
        some (n.outbox & SendingMsg)
        implies
        n in Member
}

// 4.9 If node has a Sending message in its outbox, it is in the receivers of the message
fact {
    all n: Node |
        some (n.outbox & SendingMsg)
        implies
        n in (n.outbox).rcvrs
}

// 4.10 Nodes cannot receive their own message (which means that leaders don't receive their own message)
fact {
    no Msg.rcvrs & Msg.sndr
}

// 4.11 Pending messages have no receivers
fact {
    some PendingMsg
    implies 
    no PendingMsg.rcvrs
}

// 4.12 Sent messages have receivers
fact {
    some SentMsg
    implies
    some SentMsg.rcvrs
}

run {
    #Member > 3
    #lnxt > 1
    #qnxt > 1
    #Leader.lnxt.Node > 1
    some SendingMsg
    some PendingMsg
    some SentMsg
} for 12