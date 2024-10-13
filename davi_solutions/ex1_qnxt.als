sig Node {}

sig Member in Node {
    // nxt: lone Member, // next member
    qnxt: Node -> lone Node, // node -> next in queue for membership
    // outbox: set Msg // set of messages to redirect
}

// No members in domain of Member.qnxt
fact {
    all m: Member |
        no (Member & m.qnxt.Node) 
}

// Owner of the queue must appear once in its co-domain if the list is not empty
fact {
    all m: Member |
        some m.qnxt 
        implies
        (Member & Node.(m.qnxt)) = m
}

// Nodes can only queue once
fact {
    all m: Member, n: Node |
        n !in (n.^(m.qnxt))
}

// Each node is 'pointed to' only once (including owner)
fact {
    all m:Member, n1:Node |
        lone n2: Node | n1 in n2.(m.qnxt)
}

// Each node in the queue can eventually reach the owner
fact {
    all m: Member |
        all n: Node |
            n in m.qnxt.Node 
            implies
            m in n.^(m.qnxt)
}

// Non-member nodes can only appear in the queue of one member
fact {
    all n: Node - Member |
        lone m: Member | n in m.qnxt.Node
}

fun visualizeMemberQueues[]: Node->Node {
    Member.qnxt
}

run {
    #Member > 1
    all m: Member | #m.qnxt.Node >= 2
    some n: Node | n not in (Member.qnxt.Node + Member)
} for 10
