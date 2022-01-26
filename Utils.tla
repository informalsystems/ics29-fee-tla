---- MODULE Utils ----

EXTENDS Sequences, TLC

EmptyRecord == [ a \in {} |-> "a" ]

AddEntry(record, key, value) ==
  key :> value @@ record

UpdateEntry(record, key, value) ==
  [ record EXCEPT ![key] = value ]

UpdateEntry2(record,
  key1,
  value1,
  key2,
  value2
) ==
  [ record EXCEPT
        ![key1] = value1,
        ![key2] = value2
  ]

HasKey(record, key) ==
  key \in DOMAIN record

EntryEquals(record, key, value) ==
  /\ HasKey(record, key)
  /\ record[key] = value

Concat(list1, list2) ==
  list1 \o list2

Identity(x) == x

=====
