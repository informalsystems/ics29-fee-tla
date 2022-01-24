---- MODULE Utils ----

EXTENDS Sequences, TLC

EmptyRecord == [ a \in {} |-> "a" ]

AddEntry(record, key, value) ==
  key :> value @@ record

UpdateEntry(record, key, value) ==
  [ record EXCEPT ![key] = value ]

HasKey(record, key) ==
  key \in DOMAIN record

EntryEquals(record, key, value) ==
  /\ HasKey(record, key)
  /\ record[key] = value

=====
