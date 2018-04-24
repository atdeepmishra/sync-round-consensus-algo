# Concensus problem in Distributed Systems

The project simulates the concensus problem in Distributed Systems using TLA+.

### With no Node Failures:

**Problem Statement: **

**Solution: **
As it is given in the problem statement, every progress broadcasts its initial 
value v to all other nodes in one round. After this round, each process decides 
the minimum value it received among all the nodes.

This is implemented by first defining the variables which holds (up, round, 
termination, decision, and mailbox) values of all the nodes. All nodes are ran 
using strong fairness, so that all the nodes get chance to executes its step.

The whole process is divided into two steps – PS (process send), and PR 
(process receives). When the first round beings the process initializes its value (v) 
to self id, and Q is initialized to all the nodes in the system.

Step PS: The process executes this step if it is up. During PS state process appends
its value (v) to mailbox of all the nodes including itself. It also calls the macro 
MaybeFail (however this will not fail any node when FAILNUM is set to zero). After sending
the value to all the nodes, process moves to next round.

Step PR: A node waits for all the node to move to next round before executing this step.
Once all the nodes are moved to the next round. Current process will find the min of the 
value received from all the node and set this as it's decision. After this it will terminate

To check the validity of the program it will satisfy the agreement property.
As per agreement property - Two correct processes can not commit to different decision variables.
The above program will work if there is no failure of nodes. Because all the nodes will reach the
Step PR and wait for other node to complete sending message to all. Once all the nodes have completed
sending message to all the nodes, all the node will decide the minimum value from the messages received.
Since all the nodes are receiving the value from all the nodes the decision of all the nodes will be same
However, if there is a node failure. The failed node might have sent its minimum value to some nodes
and failed before sending minimum to all the nodes. In this case, if the failed node value was 
least of all the nodes, the minimum calculated by few nodes (who received this value) will differ from others.
Hence the agreement property is violated in the current model if there is any failure.


### With N Nodes Failures:

**Problem Statement: ** The Aggrement property and validitiy will fail if there is any node failure while sending the message to other nodes. Single round of message exchange will not help to reach the consensue by all the parties.

In brief - we need to run for multiple rounds to establish the consences. However, every nodes need  to identify when to go for the next round and when to stop.

**Solution: ** This problem can be solved by observing the behaviour of nodes' mail box and the decision in any two consecutive rounds of the node. If we closly monitor both these properties. If there is any failure the message count received by a node will be lesser than the previous round. Or the decision made in previous round would be different from  current round decision of a node. In general, either of the parameters will differ is there is any failure. By looking at the difference in both the property (mail box size, and decisions) of the node we can identify whether to go for next round or not.

Based on the above analogy, project [syncConwithFailure](consensus-with-failure/syncCon2.toolbox/Model_1/syncCon2.tla) implements the solution for reaching concensus with N nodes failure in distributed systems.
