sig Node {
    outbox: set Msg // Own messages before being broadcasted and messages it must redirect
}

sig Member in Node {
    nxt: lone Member, // next member
    // qnxt: Node -> lone Node, // node -> next in queue for membership
}

one sig Leader in Member {
    // lnxt: Node -> lone Node // leader -> leader queue
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
    Message status consistency
*/ 

// Sent, Sending and Pending are disjoint
fact {
    disj[SentMsg, SendingMsg, PendingMsg]
}

// There can be one or zero sending message at a time
fact {
    lone SendingMsg
}

// Sending messages have the current Leader as the sender
fact {
    some SendingMsg
    implies
    SendingMsg.sndr = Leader
}

// Sending Messages need to have at least some receiver
fact {
    some SendingMsg
    implies
    some SendingMsg.rcvrs
}

// Sending Messages need to be in one member's outbox
fact {
    some SendingMsg
    implies
    SendingMsg in Node.outbox
}

// Outbox contains no sent messages
fact {
    no Node.outbox & SentMsg
}

// Outbox contains all pending messages of the current node
fact {
    all n: Node |
        (sndr.n & PendingMsg) in n.outbox
}

// If node has a Sending message in its outbox, node is a member
fact {
    all n: Node |
        some (n.outbox & SendingMsg)
        implies
        n in Member
}

// If node has a Sending message in its outbox
// it is in the receivers of the message
fact {
    all n: Node |
        some (n.outbox & SendingMsg)
        implies
        n in (n.outbox).rcvrs
}

// Nodes cannot receive their own message
// (which means that leaders don't receive their own message)
fact {
    no Msg.rcvrs & Msg.sndr
}

// Pending messages have no receivers
fact {
    some PendingMsg
    implies 
    no PendingMsg.rcvrs
}

// Sent messages have receivers
fact {
    some SentMsg
    implies
    some SentMsg.rcvrs
}


run {
    #Member > 3
    #Leader > 0
    #Msg > 2
    // #Leader.lnxt.Node > 1
    // some LQueue
    some n: Node | n in (Node-Member)
    // some m: Member | m !in (Leader.lnxt.Node)
} for 12