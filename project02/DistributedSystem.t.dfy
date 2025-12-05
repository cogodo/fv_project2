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
  ghost predicate HostAction(c: Constants, v: Variables, v': Variables, hostid: HostId, event: Event)
  {
    && v.WF(c)
    && v'.WF(c)
    && hostid < |c.hosts|
    && (exists msgOps ::
      && Host.NextStep(c.hosts[hostid], v.hosts[hostid], v'.hosts[hostid], msgOps, event)
      && Network.Next(c.network, v.network, v'.network, msgOps))
  }

  // TODO: ask Ivan?
  // Represent next step --> step is now event tho....
  ghost predicate Next(c: Constants, v: Variables, v': Variables, event: Event)
  {
    && v.WF(c)
    && v'.WF(c)
    && exists hostid :: HostAction(c, v, v', hostid, event)
  }
/*}*/
}
