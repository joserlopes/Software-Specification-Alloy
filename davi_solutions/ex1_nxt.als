sig Node {}

sig Member in Node {
    nxt: lone Member, // next member
    // qnxt: Node -> lone Node, // node -> next in queue for membership
    // outbox: set Msg // set of messages to redirect
}

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

run { #Member=5 #Node=7 } for 10 // cant find instance with 8 members.. why? 
