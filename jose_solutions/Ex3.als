open Ex2

pred fairnessMemberApplication[] {
    all m: Node, n: Node |
        eventually always (m in Member && n != m && n !in Node.(~(Member.qnxt)) && n !in Member.(^nxt))
            implies
        (always eventually
            memberApplication[m, n])
}

pred fairnessMemberPromotion[] {
    all m: Node, nFirst: Node |
        eventually always (m in Member && nFirst = m.~(m.qnxt))
            implies
        (always eventually
            memberPromotion[m])
}

pred fairnessLeaderApplication[] {
    all m: Node |
        eventually always (m in Member && m != Leader && m !in LQueue)
            implies
        (always eventually
            leaderApplication[m])
}

pred fairnessLeaderPromotion[] {
    all mFirst: Node |
        eventually always (mFirst in Member && mFirst = Leader.~(Leader.lnxt) && no (sndr.Leader & PendingMsg) && no SendingMsg)
            implies
        (always eventually
            leaderPromotion[])
}

pred fairnessBroadcastInitialisation[] {
    all msg: Msg |
        eventually always (msg.sndr = Leader && msg in PendingMsg && msg in Leader.outbox && Leader.nxt != Leader)
            implies
        (always eventually
            broadcastInitialisation[msg])
}

pred fairnessMessageRedirect[] {
    all m: Node, msg: Msg |
        eventually always (m in Member && msg in SendingMsg && m != Leader && m.nxt != Leader && msg in m.outbox && msg.sndr = Leader)
            implies
        (always eventually
            messageRedirect[m, msg])
}

pred fairnessBroadcastTermination[] {
    all msg: Msg, mLast: Node |
        eventually always (mLast in Member && msg in SendingMsg && msg.sndr = Leader && mLast.nxt = Leader && msg in mLast.outbox)
            implies
        (always eventually
            broadcastTermination[msg])
}

pred fairness[] {
    fairnessMemberApplication[]
    &&
    fairnessMemberPromotion[]
    &&
    fairnessLeaderApplication[]
    &&
    fairnessLeaderPromotion[]
    &&
    fairnessBroadcastInitialisation[]
    &&
    fairnessMessageRedirect[]
    &&
    fairnessBroadcastTermination[]
}

pred allBroadcastsTerminate[] {
    Msg = SentMsg
    // all msg: Msg |
    //     once msg in PendingMsg implies eventually msg in SentMsg
}

pred noExits[] {
    always no m: Member, n: Node | nonMemberExit[m, n]
    always no m: Member | memberExit[m]
}

fun visualizeMemberQueues[]: Node->Node {
    Member.qnxt
}

fun visualizeLeaderQueues[]: Node->Node {
    Leader.lnxt
}

run {
    fairness[] && #Node > 1
}

run {
    fairness[] && noExits[] && #Node > 1
} for 20 steps

assert weakFairness {
    (fairness[] && #Node > 1) implies (eventually allBroadcastsTerminate[])
}

assert strongFairness {
    (fairness[] && noExits[] && #Node > 1) implies (eventually allBroadcastsTerminate[])
}

check weakFairness

check strongFairness
