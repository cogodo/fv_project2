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
      && |hosts| > 0
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

  // Demonstrate a Host taking an event action and all other hosts stay unchanged
  ghost predicate HostAction(c: Constants, v: Variables, v': Variables, hostid: HostId, event: Event, msgOps: Network.MessageOps)
  {
    && v.WF(c)
    && v'.WF(c)
    && hostid < |c.hosts|
    && Host.Next(c.hosts[hostid], v.hosts[hostid], v'.hosts[hostid], msgOps, event)
    // all other hosts stay unchanged
    && (forall otherHost: HostId | otherHost < |c.hosts| && otherHost != hostid :: v.hosts[otherHost] == v'.hosts[otherHost])
  }

  // Demonstrate a Next for HostAction and Network being the same event
  ghost predicate Next(c: Constants, v: Variables, v': Variables, event: Event)
  {
    && v.WF(c)
    && v'.WF(c)
    && (exists hostid, msgOps :: HostAction(c, v, v', hostid, event, msgOps) && Network.Next(c.network, v.network, v'.network, msgOps))
  }
/*}*/
}
