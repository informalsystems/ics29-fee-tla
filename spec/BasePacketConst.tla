----- MODULE BasePacketConst -----

EXTENDS
  Types,
  BaseChannelConst

CONSTANTS
  \* @type: Set(ADDRESS);
  AllUsers,

  \* @type: Set(SEQUENCE);
  AllSequences,

  \* @type: Set(Str);
  BasePayloads,

  \* @type: Set(Str);
  BaseAcks,

  \* @type: SEQUENCE;
  NullSequence

=====
