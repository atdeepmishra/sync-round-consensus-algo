# Concensus problem in Distributed Systems

The project simulates the concensus problem in Distributed Systems using TLA+.

### With no Node Failures:

**Problem Statement:** How to achieve concensus in Distributed System.

**Solution:** In a synchronous network, the concensus can be reached in single round of message exchange. Every process broadcasts (to all other processes, including itself) its initial value. After one round , each process decides on the minimum value it
received. This will result into every process having same minimun value.

Based on above algorithm, project [syncConwithnoFailure](consensus-with-no-failure/syncCon1.toolbox/Model_1/syncCon1.tla) implements the above algorithm and checks for Aggrement and validity property.

##

### With N Nodes Failures:

**Problem Statement:** The Aggrement property and validitiy will fail if there is any node failure while sending the message to other nodes. Single round of message exchange will not help to reach the consensue by all the parties.

In brief - we need to run for multiple rounds to establish the consences. However, every nodes need  to identify when to go for the next round and when to stop.

**Solution:** This problem can be solved by observing the behaviour of nodes' mail box and the decision in any two consecutive rounds of the node. If we closly monitor both these properties. If there is any failure the message count received by a node will be lesser than the previous round. Or the decision made in previous round would be different from  current round decision of a node. In general, either of the parameters will differ is there is any failure. By looking at the difference in both the property (mail box size, and decisions) of the node we can identify whether to go for next round or not.

Based on the above analogy, project [syncConwithFailure](consensus-with-failure/syncCon2.toolbox/Model_1/syncCon2.tla) implements the solution for reaching concensus with N nodes failure in distributed systems.
