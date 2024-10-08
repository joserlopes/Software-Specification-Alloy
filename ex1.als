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


// topological constraints: ensure network is valid
/*
1. Leader
- There is only one leader OK

2. Members
2.1 Queue for membership
- Queue for membership consists only of non-members
- Queue for membership ends in current Member

2.2 The circle (Member.nxt)
- Members can only have one target in the circle OK
- There must be one nxt relation that ends in the Leader
- It loops! Every member is reachable from every other member
- No loops within the loop: Members apear only once in the circle

4. Leadership queue
- Queue must end in the leader
- The leader is only once at the queue
- Queue only has members 
- Queue cannot have repeated Members

5.  
- Outsiders cannot be in the leadership queue
- Outsiders must be in one and only one queue. (i.e. must be in a queue + only one queue)

*/
// message consistency constraints: ensure messages are in a consistent state
/*

1. Pending
- Pending messages cannot be in any outbox (OK, see Sending)
- Pending message's rcvrs must be empty

2. Sending
- Outboxes can only contain Sending messages (no Pending, no Sent)
- The sndr of a sending message must be the current leader

3. Sent
- Sent messages cannot be in any outbox OK
- Sent messages must have been in its sndr outbox (received by the leader)
- Sent messages must have all members from the circle in its rcvrs

*/