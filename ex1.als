sig Node {}

sig Member in Node {
    nxt: lone Member, // next member
    qnxt: Node -> lone Node, // node -> next in queue for membership
    outbox: set Msg // set of messages to redirect
}
one sig Leader in Member {
    lnxt: Node -> lone Node // leader -> leader queue
}

sig LQueue in Member {} // set of nodes in leader queue

abstract sig Msg {
    sndr: Node, // Sender node
    rcvrs: set Node // Nodes messages was delivered
}

sig SentMsg, SendingMsg, PendingMsg extends Msg {}
