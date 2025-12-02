include "IMapHelpers.t.dfy"
include "Types.t.dfy"
//#extract Types.t.template inherit Types.t.dfy

// The application spec for this system is a key-value store
// that maintains a map of int keys to int values.
// The type of the state in this state machine is simply a total imap: one in
// which every possible key is in the domain.
// The user-visible actions are Get and Put operations.
// Get accepts a key and returns a value.
// Put accepts a key and a value and returns nothing.
//
// You should write a synchronous spec that produces the world-visible
// events defined in Types.t.dfy: Get and Put (plus NoOp).

module AtomicKVSpec {
  import opened IMapHelpers
  import opened Types

  datatype Constants = Constants()  // don't need any here
  datatype Variables = Variables(
  /*{*/
    mp: imap<int, int>
  /*}*/
  )

  // The initial map should assign the value zero to every key.
  // Be sure to check out IMapHelpers.t.dfy. It's helpful.
  ghost predicate Init(c: Constants, v: Variables) {
  /*{*/
    && v.mp == ZeroMap() 
  /*}*/
  }

  /*{*/
  // Model the Get event to accept a key and return a value
  ghost predicate GetEvt(v: Variables, v': Variables, key: int, value: int) 
  {
    && IsFull(v.mp)
    && value == v.mp[key]
    && v' == v
  }

  // Model the Put event to update the key's value 
  ghost predicate PutEvt(v: Variables, v': Variables, key: int, value: int) 
  {
    && IsFull(v.mp)
    // v' is updated such that v's map at key value is now set to "value"
    // First, remove the original key value from v.mp
    && var keyset: iset<int> := iset {key};
    var rm_mp := MapRemove(v.mp, keyset);

    // Second, create a temp imap with key, value
    var t := imap[key := value];

    // Last, union the maps and prefer the original map (to take in the new key, value)
    var tmp := IMapUnionPreferLeft(v.mp, t);
    && v' == v.(mp := tmp)
  }

  /*}*/

ghost predicate NextStep(c: Constants, v: Variables, v': Variables, event: Event) {
  /*{*/
    match event {
      case Get(key, value) => GetEvt(v, v', key, value)
      case Put(key, value) => PutEvt(v, v', key, value)
      case NoOp => v' == v
    }
  /*}*/
}

  ghost predicate Next(c: Constants, v: Variables, v': Variables, event: Event) {
    // All the nondeterminism is encoded in `event`! No `exists` required.
    NextStep(c, v, v', event)
  }
}
