----- MODULE Types ----

\* @typeAlias: CHAIN_ID = Str;
\* @typeAlias: ADDRESS = Str;
\* @typeAlias: TRANSFER = [
\*    chain_id: CHAIN_ID,
\*    sender: ADDRESS,
\*    receiver: ADDRESS,
\*    amount: Int
\* ];
\* @typeAlias: BALANCE_KEY = << CHAIN_ID, ADDRESS >>;
\* @typeAlias: BANK_BALANCES = (BALANCE_KEY -> Int);
Aliases == TRUE

=====
