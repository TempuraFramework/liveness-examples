# Liveness Examples in Ivy

| File Name | Description | Property | Fairness Conditions | Rule | Remarks | Model OK? | Proof OK? | Manual Automation OK?| Auto Automation OK?|
|-----------|-------------|----------|---------------------|------|---------|-----------|-----------|---------------|----------|
|`one_queue.ivy`| Single FIFO queue | $\square\forall X. begun(X) -> \Diamond done(X)$   | $\square \diamond recv$ | AUTO2 | n/a | Yes | Yes | Yes | No |
|`two_queues.ivy`|Two FIFO queues concatenated | $\square \forall X. begun1(X) -> \Diamond done2(X)$ | $\square\Diamond recv1 \wedge \square\Diamond recv2$ | AUTO5 | n/a | Yes | Yes | Yes | No |
|`two_colored_queue.ivy`| FIFO queue with each message having two types. There are two corresponding polling operations, blocking based on message type. | $\square \forall X. begun(X) -> \Diamond done(X)$ | $\square\Diamond recv $ | AUTO5 | n/a | Yes | Yes | Somewhat | No | 
| `token_ring.ivy` | Token ring mutex protocol modeled as a fixed linked list | ... | ... | LEX | needs `complete=fo` | Yes | Yes | Yes | No |
| `token_ring_btw.ivy` | Token ring mutex protocol modeled using the between relation | ... | ... | AUTO2 | n/a | Yes | Yes | Yes | No |
| `ticket.ivy` | Ticket mutex protocol | ... | ... | AUTO5 | n/a | Yes | Yes | Yes | No | 
| `ticket_ranking.ivy` | Ticket mutex protocol | ... | ... | LEX | n/a | Yes | Yes | Yes | No |
|`ring_of_queues.ivy`| $n$ FIFO queues concatenated with each other. | $\square \forall X, I. begun(X,I) -> \Diamond done(X, N-1)$ | $\forall I<N. \square \Diamond recv(I)$ | ?? | Expressing an invariant like $\forall I. begun(X, I + 1) -> done(X, I)$ takes us out of FAU because of $+$ | No | No | No | No |
|`ticket.ivy` | Ticket Protocol | $\forall T,X. \square pc2(T) \wedge m(T,X) -> \Diamond pc3(T)$ | $\forall T. \square (\Diamond scheduled \wedge scheduled.value = T)$ | AUTO5 | Parametrized fairness condition | Yes | Yes | No | No | 
| `abp.ivy` | Alternating Bit Protocol | ??? | ??? | ??? | Need to figure this out | No | No | No | No |
