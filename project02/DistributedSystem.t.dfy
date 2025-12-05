include "Network.t.dfy"
//#extract Network.t.template inherit Network.t.dfy
include "Host.v.dfy"
//#extract Host.v.template inherit Host.v.dfy

module DistributedSystem {
  import opened UtilitiesLibrary
  import opened Types
  import Network
  import Host

  type HostId = Network.HostId

/*{*/
  datatype Constants = Constants(
    hosts: seq<Host.Constants>,
    network: Network.Constants
  )
  {
    ghost predicate WF() {
      && (forall i:nat | i < |hosts| :: hosts[i].totalHosts == |hosts|)
      && (forall i:nat | i < |hosts| :: hosts[i].id == i)
    }
  }

  datatype Variables = Variables(
    hosts: seq<Host.Variables>,
    network: Network.Variables
  )
  {
    ghost predicate WF(c: Constants) {
      && c.WF()
      && |hosts| == |c.hosts|
      && forall i:nat | i < |hosts| :: hosts[i].WF(c.hosts[i])
    }
  }

  // Initialize Init for Host and Network
  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && Network.Init(c.network, v.network)
    && forall i:nat | i < |v.hosts| :: Host.Init(c.hosts[i], v.hosts[i])
  }

  // TODO: Figure out how to repesent "Host Actions" with events (Get, Put) --> Noop is sending key,value pair
  ghost predicate HostAction(c: Constants, v: Variables, v': Variables, hostid: HostId)
  {
    true // fix me
  }

  // Handling Put to update the Host's Variables (key and value)
  function PutVariableUpdate(c: Constants, v: Variables, v': Variables, evt: Event) : Variables
  {
    // From network, find the Put message (which has the key and value to update)
    // TODO: can there be multiple Put message in network? Or can we assume there will be a put message at this point?
    var msg :| msg in v.network.inFlightMessages && msg.Put?;
    
    // From our hosts, find host with that key
    

    // Update this host's key with new value with the Put evt
    // HandlePut(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) 

    
    v
  }

  // Handling a Noop event, which means hosts are sharing key and value with other host
  function NoOpVariableUpdate(c: Constants, v: Variables, v': Variables, evt: Event) : Variables
  {
    v
  }

  function ApplyEvents(c: Constants, v: Variables, v': Variables, evt: Event): Variables
  {
    // TODO: FIX MEEE
    match evt
      case Get(key, val) => v
      case Put(key, val) => PutVariableUpdate(c, v, v', evt)
      case NoOp => NoOpVariableUpdate(c, v, v', evt)
    
  }
  // TODO: ask Ivan?
  // Represent next step --> step is now event tho....
  ghost predicate Next(c: Constants, v: Variables, v': Variables, event: Event)
  {
    v' == ApplyEvents(c, v, v', event)
  }
/*}*/
}
