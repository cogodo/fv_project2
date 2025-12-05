include "UtilitiesLibrary.t.dfy"
include "IMapHelpers.t.dfy"
include "Types.t.dfy"
//#extract Types.t.template inherit Types.t.dfy
include "MessageType.v.dfy"
//#extract MessageType.v.template inherit MessageType.v.dfy
include "Network.t.dfy"
//#extract Network.t.template inherit Network.t.dfy

//
// Your protocol should capture the idea that keys "live" on different hosts
// *and can move around* from host to host. So, in addition to implementing
// client-visible actions as described in AtomicKVSpec, each host should have a way
// to send part of its state to another host, and to receive the corresponding
// message from another sender. (The messages can move a batch of key-value
// pairs, or a single pair at a time; neither is particularly harder than the
// other.)
//
// Obviously, the hosts must be aware of which fraction of the keyspace they
// own at any given time, so that a host doesn't try to service a Get or Put
// request when the "real state" is off at some other host right now.
//
// Initially host 0 should own all the keys.
//
// Don't forget about the helper functions in IMapHelpers.t.dfy. They can be
// quite useful!

module Host {
  import opened UtilitiesLibrary
  import opened IMapHelpers
  import opened Types
  import opened MessageType
  import Network

  type HostId = Network.HostId

/*{*/
  // Replace these definitions with more meaningful ones that capture the operations
  // of a key-value store described above.
  datatype Constants = Constants(
    id: HostId,
    totalHosts: nat
  )
  datatype Variables = Variables(
    mp: map<int, int>
  ) 
  {
    ghost predicate WF(c: Constants) {
      c.id < c.totalHosts
    }
  }
  
  // Initially, host 0 should own all the keys
  ghost predicate Init(c: Constants, v: Variables)
  { 
    && v.WF(c)
    && if c.id == 0 then forall i:int :: i in v.mp && v.mp[i] == 0 else v.mp == map[]
  }
  
  // Other Host Actons Sending the (Get, Put, KeyValue) Messages
  ghost predicate IdxInMap(v: Variables, key: int)
  {
    key in v.mp
  }

  // Handle a Get operation locally
  ghost predicate HandleGet(c: Constants, v: Variables, v': Variables, key: int)
  {
    && v.WF(c)
    && IdxInMap(v, key)
    && v == v'// Get does not change anything about our state
  }
  
  // Upon receiving a Put Message, update the key to have new value
  ghost predicate HandlePut(c: Constants, v: Variables, v': Variables, key: int, value: int) 
  {
    && v.WF(c)
    && IdxInMap(v, key)
    && v' == v.(mp := v.mp[key := value])
  }

  // Send to host's current state for key, value and remove from host's map after send
  ghost predicate SendToHost(c: Constants, v: Variables, v': Variables, msgOps: Network.MessageOps) 
  {
    && v.WF(c)
    && msgOps.recv.None?
    && msgOps.send.Some?
    && var sendMsg := msgOps.send.value;
    && sendMsg.KeyValue?
    && sendMsg.dest != c.id 
    && sendMsg.dest < c.totalHosts
    && sendMsg.from == c.id
    && IdxInMap(v, sendMsg.dest)
    && v.mp[sendMsg.dest] == sendMsg.value
    && v' == v.(mp := map i:int | i in v.mp && i != sendMsg.key :: v.mp[i])
  }

  // Receive a host's state, update/add our own map with new key, value
  ghost predicate RecvFromHost(c: Constants, v: Variables, v': Variables, msgOps: Network.MessageOps) 
  {
    && v.WF(c)
    && msgOps.send.None?
    && msgOps.recv.Some?
    && var recvMsg := msgOps.recv.value;
    && recvMsg.KeyValue?
    && recvMsg.from != c.id
    && recvMsg.from < c.totalHosts
    && recvMsg.dest == c.id
    && !(recvMsg.key in v.mp)
    && var t := map[recvMsg.key := recvMsg.value];
    && v' == v.(mp := v.mp + t)
  }
  
  // Model the Host taking a next step with events (restrict)
  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: Network.MessageOps, event: Event)
  {
    || (exists key, value :: HandleGet(c, v, v', key) && event == Event.Get(key, value))
    || (exists key, value :: HandlePut(c, v, v', key, value) && event == Event.Put(key, value))
    || (SendToHost(c, v, v', msgOps) && event == NoOp())
    || (RecvFromHost(c, v, v', msgOps) && event == NoOp())
  }
/*}*/
}
