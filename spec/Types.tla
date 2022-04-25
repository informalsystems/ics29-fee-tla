----- MODULE Types ----

\* @typeAlias: CHANNEL_ID = Str;
\* @typeAlias: ADDRESS = Str;
\* @typeAlias: TRANSFER = [
\*    chain_id: CHAIN_ID,
\*    sender: ADDRESS,
\*    receiver: ADDRESS,
\*    amount: Int
\* ];
\* @typeAlias: CHANNEL_STATE = [
\*    handshake_state: Str,
\*    counterparty_chain_id: CHAIN_ID,
\*    counterparty_channel_id: CHANNEL_ID,
\*    versions: Seq(Str)
\* ];
\* @typeAlias: PACKET_KEY = <<
\*    CHAIN_ID,
\*    CHANNEL_ID,
\*    Str
\* >>;
\* @typeAlias: PACKET = [
\*    chain_id: CHAIN_ID,
\*    counterparty_chain_id: CHAIN_ID,
\*    channel_id: CHANNEL_ID,
\*    counterparty_channel_id: CHANNEL_ID,
\*    sequence: Str,
\*    payload: Str
\* ];
\* @typeAlias: ESCROW = [
\*    receive_fee: Int,
\*    ack_fee: Int,
\*    timeout_fee: Int,
\*    refund_address: ADDRESS
\* ];
\* @typeAlias: RELAY = [
\*    event: Str,
\*    relayer: ADDRESS,
\*    chain_id: CHAIN_ID,
\*    channel_id: CHANNEL_ID,
\*    sequence: Str
\* ];
\* @typeAlias: BALANCE_KEY = << CHAIN_ID, ADDRESS >>;
\* @typeAlias: BANK_BALANCES = (BALANCE_KEY -> Int);
Aliases == TRUE

=====
