# Liveness Examples in Ivy

| File Name | Description | Property | Fairness Conditions | Rule | Remarks | Model OK? | Proof OK? | Manual Automation OK?| Auto Automation OK?|
|-----------|-------------|----------|---------------------|------|---------|-----------|-----------|---------------|----------|
|`one_queue.ivy`| Single unbounded FIFO queue, non-consecutive issue timestamps | $\square\forall X. begun(X) -> \Diamond done(X)$   | $\square \diamond recv$ | AUTO2 | n/a | Yes | Yes | Yes | No |
| `one_queue_unord.ivy` | Unbounded unordered channel | same as above | $\forall X. \square\diamond recv(X)$ | AUTO2 | n/a | Yes | Yes | Yes | No |
|`pingpong1.ivy`| Single unbounded FIFO queue, consecutive issue timestamps | same as above | same as above | AUTO2 | n/a | Yes | Yes | Yes | No |
|`pingpong2.ivy`| Blocking unbouned FIFO queue, at most one element in flight | same as above | same as above | AUTO2 | n/a | Yes | Yes | Yes | No |
|`pingpong3.ivy`| Blocking unbounded FIFO queue with invariant showing at most one element in flight | same as above | same as above | finite | n/a | Yes | Yes | Yes | No |
|`two_queues.ivy`|Two FIFO queues concatenated | $\square \forall X. begun1(X) -> \Diamond done2(X)$ | $\square\Diamond recv1 \wedge \square\Diamond recv2$ | AUTO5 | n/a | Yes | Yes | Yes | No |
|`two_colored_queue.ivy`| FIFO queue with each message having two types. There are two corresponding polling operations, blocking based on message type. | $\square \forall X. begun(X) -> \Diamond done(X)$ | $\square\Diamond recv $ | AUTO5 | n/a | Yes | Yes | Somewhat | No | 
| `token_ring.ivy` | Token ring mutex protocol modeled as a fixed linked list | ... | ... | LEX | ... | Yes | Yes | Yes | No |
| `token_ring_btw.ivy` | Token ring mutex protocol modeled using the between relation and no witness for token holder | ... | ... | AUTO2 | n/a | Yes | Yes | Yes | No |
| `token_ring_btw_instr.ivy` | Token ring mutex protocol modeled using between relation and witness for token holder | ... | ... | AUTO2 | n/a | Yes | Yes | Yes | No |
| `ticket.ivy` | Ticket mutex protocol | ... | ... | AUTO5 | n/a | Yes | Yes | Yes | No | 
| `ticket_ranking.ivy` | Ticket mutex protocol | ... | ... | LEX | n/a | Yes | Yes | Yes | No |
| `abp.ivy` | Alternating Bit Protocol | ??? | ??? | ??? | Need to figure this out | No | No | No | No |
