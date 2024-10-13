sig Node {}

sig Member in Node {
    // nxt: lone Member, // next member
    // qnxt: Node -> lone Node, // node -> next in queue for membership
    // outbox: set Msg // set of messages to redirect
}

one sig Leader in Member {
    lnxt: Node -> lone Node // leader -> leader queue
}

sig LQueue in Member {} // set of nodes in leader queue


// LQueue has all members in Leaders queue
fact {
    all m: Member |
        m in Leader.lnxt.Node
        implies
        m in LQueue
}

// No non-members or leader in domain of Leader.lnxt
fact {
    no (((Node-Member)+Leader) & Leader.lnxt.Node)
}

// No non-members in the codomain of Leader.lnxt
fact {
    no ((Node-Member) & Node.(Leader.lnxt)) 
}

// Owner of the queue must appear once in its co-domain if the list is not empty
fact {
    some Leader.lnxt 
        implies
    (Leader in Node.(Leader.lnxt))
}

// Each member can only queue once 
fact {
    all m:Member |
        m in Leader.lnxt.Node
        implies
        one m & Leader.lnxt.Node
}

// Each node is 'pointed to' only once (including owner)
fact {
    all m1:Member |
        lone m2: Node | m1 in m2.(Leader.lnxt)
}

// Each node in the queue can eventually reach the leader
fact {
    all m: Member |
        m in Leader.lnxt.Node
        implies
        Leader in m.^(Leader.lnxt)
}

fun visualizeLeaderQueues[]: Node->Node {
    Leader.lnxt
}

run {
    #Member > 3
    #Leader > 0
    #Leader.lnxt.Node > 1
    some LQueue
    some n: Node | n in (Node-Member)
    some m: Member | m !in (Leader.lnxt.Node)
} for 12
