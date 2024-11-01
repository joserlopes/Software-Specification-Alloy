sig Node {}

sig Member in Node {
    nxt: lone Member, // next member
    qnxt: Node -> lone Node, // node -> next in queue for membership
    // outbox: set Msg // set of messages to redirect
}

one sig Leader in Member {
    // lnxt: Node -> lone Node // leader -> leader queue
}

// sig LQueue in Member {} // set of nodes in leader queue

// abstract sig Msg {
    // sndr: Node, // Sender node
    // rcvrs: set Node // Nodes messages was delivered
// }

// sig SentMsg, SendingMsg, PendingMsg extends Msg {}

/*
    1. Members form a single ring with each member pointing to another member or itself
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

// 1.3 Every member can reach every other one through nxt
// TODO: Change this fact to point free notation
fact {
    all m1, m2: Member |
        m1 in (m2.^nxt) && m2 in (m1.^nxt)
}

// Nodes in every qnxt can't be Members
fact {
    all m1: Member |
        no (Member & m1.qnxt.Member)
}

// 1.1 All members must have a nxt and be the nxt of someone
fact {
    Member = nxt.Member
    &&
    Member = Member.nxt
}
// 
fact {
}

fun visualizeMemberQueues[]: Node->Node {
    Member.qnxt
}

run { #Member=3 } for 10 // cant find instance with 8 members.. why? 
