module MessageType {
  datatype Message =
/*{*/
    | Get(key: int, value: int)
    | Put(key: int, value: int)
    | KeyValue(key: int, value: int, dest: nat, from: nat)
/*}*/
}
