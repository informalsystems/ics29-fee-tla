---- MODULE Utils ----

EXTENDS Sequences, TLC

\* @type: a => ( b -> a );
EmptyRecord(x) == [ a \in {} |-> x ]

\* @type: ( (a -> b), a, b ) => (a -> b);
AddEntry(record, key, value) ==
  key :> value @@ record

\* @type: ( (a -> b), a, b ) => (a -> b);
UpdateEntry(record, key, value) ==
  [ record EXCEPT ![key] = value ]

\* @type: ( (a -> b), a, b, a, b ) => (a -> b);
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

\* @type: ( (a -> b), a ) => (a -> b);
DeleteEntry(record, key) ==
  [ k \in DOMAIN record \ { key } |-> record[key] ]

\* @type: ( (a -> b), a ) => Bool;
HasKey(record, key) ==
  key \in DOMAIN record

\* @type: ( (a -> b), a, b ) => Bool;
EntryEquals(record, key, value) ==
  /\ HasKey(record, key)
  /\ record[key] = value

\* @type: (Seq(a), Seq(a)) => Seq(a);
Concat(list1, list2) ==
  list1 \o list2

\* @type: a => a;
Identity(x) == x

=====
