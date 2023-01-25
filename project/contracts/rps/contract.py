from pyteal import *
from pyteal.ast.bytes import Bytes
from pyteal_helpers import program

def approval():
    # locals
    local_opponent = Bytes("opponent")  # byteslice
    local_wager = Bytes("wager")  # uint64
    local_commitment = Bytes("commitment")  # byteslice
    local_reveal = Bytes("reveal")  # byteslice

    op_challenge = Bytes("challenge")
    op_accept = Bytes("accept")
    op_reveal = Bytes("reveal")

    @Subroutine(TealType.none)
    def reset(account: Expr):
        return Seq(
            App.localPut(account, local_opponent, Bytes("")),
            App.localPut(account, local_wager, Int(0)),
            App.localPut(account, local_commitment, Bytes("")),
            App.localPut(account, local_reveal, Bytes("")),
        )

    @Subroutine(TealType.uint64)
    def is_empty(account: Expr):
        return Return(
            And(
                App.localGet(account, local_opponent) == Bytes(""),
                App.localGet(account, local_wager) == Int(0),
                App.localGet(account, local_commitment) == Bytes(""),
                App.localGet(account, local_reveal) == Bytes(""),
            )
        )

    @Subroutine(TealType.uint64)
    def is_valid_play(play: Expr):
        first_letter = ScratchVar(TealType.bytes)
        return Seq(
            first_letter.store(Substring(play, Int(0), Int(1))),
            Return(
                Or(
                    first_letter.load() == Bytes("r"),
                    first_letter.load() == Bytes("p"),
                    first_letter.load() == Bytes("s"),
                )
            ),
        )

    @Subroutine(TealType.none)
    def create_challenge():
        return Seq(
            # basic sanity checks
            program.check_self(
                group_size=Int(2),
                group_index=Int(0),
            ),
            program.check_rekey_zero(2),
            Assert(
                And(
                    # second transaction is wager payment
                    # mi aspetto un gruppo di due transazioni di cui la seconda deve essere
                    # la scommessa di chi crea la challenge quindi devo controllare che
                    # sia stata effettuata
                    Gtxn[1].type_enum() == TxnType.Payment,
                    Gtxn[1].receiver() == Global.current_application_address(),
                    # non deve rimandare a nessun indirizzo (check di sicurezza) 
                    Gtxn[1].close_remainder_to() == Global.zero_address(),

                    # second account has opted-in
                    App.optedIn(Txn.accounts[1], Global.current_application_id()),
                    # check if any of the accounts is involved in other rps match
                    is_empty(Txn.sender()),
                    is_empty(Txn.accounts[1]),

                    # commitment check
                    Txn.application_args.length() == Int(2),
                )
            ),
            # dopo aver fatto i check vari nell'assert, posso memorizzare questi valori
            # dentro alle variabili locali 
            App.localPut(Txn.sender(), local_opponent, Txn.accounts[1]),
            App.localPut(Txn.sender(), local_wager, Gtxn[1].amount()),
            App.localPut(Txn.sender(), local_commitment, Txn.application_args[1]),
            Approve(),
        )

    @Subroutine(TealType.none)
    def accept_challenge():
        return Seq(
            # basic sanity checks
            program.check_self(
                group_size=Int(2),
                group_index=Int(0),
            ),
            # basic sanity checks
            program.check_rekey_zero(2),
            Assert(
                And(
                    # second (opponent) account has opted-in
                    App.optedIn(Txn.accounts[1], Global.current_application_id()),
                    # second account has challenged this account
                    App.localGet(Txn.accounts[1], local_opponent) == Txn.sender(),
                    # second transaction is wager match
                    Gtxn[1].type_enum() == TxnType.Payment,
                    Gtxn[1].receiver() == Global.current_application_address(),
                    Gtxn[1].close_remainder_to() == Global.zero_address(),
                    Gtxn[1].amount() == App.localGet(Txn.accounts[1], local_wager),
                    # no commitment on accept, just instant reveal
                    Txn.application_args.length() == Int(2),
                    # validate play
                    is_valid_play(Txn.application_args[1]),
                )
            ),
            App.localPut(Int(0), local_opponent, Txn.accounts[1]),
            App.localPut(Int(0), local_wager, Gtxn[1].amount()),
            App.localPut(Int(0), local_reveal, Txn.application_args[1]),
            Approve(),
        )

    @Subroutine(TealType.uint64)
    def play_value(p: Expr):
        first_letter = ScratchVar()
        return Seq(
            first_letter.store(Substring(p, Int(0), Int(1))),
            Return(
                Cond(
                    [first_letter.load() == Bytes("r"), Int(0)],
                    [first_letter.load() == Bytes("p"), Int(1)],
                    [first_letter.load() == Bytes("s"), Int(2)],
                )
            ),
        )

    # modificata con tutorial youtube
    @Subroutine(TealType.uint64)
    def winner_account_index(challenger_play: Expr, opponent_play: Expr):
        return Return(
            Cond(
                [(opponent_play + Int(1)) % Int(3) == challenger_play, Int(0)],
                [(challenger_play + Int(1)) % Int(3) == opponent_play, Int(1)],
            )
        )

    @Subroutine(TealType.none)
    def send_reward(account_index: Expr, amount: Expr):
        return Seq(
            InnerTxnBuilder.Begin(),
            InnerTxnBuilder.SetFields({
                    TxnField.type_enum: TxnType.Payment,
                    TxnField.receiver: Txn.accounts[account_index],
                    TxnField.amount: amount,
            }),
            InnerTxnBuilder.Submit(),
        )

    @Subroutine(TealType.none)
    def reveal():
        wager = ScratchVar(TealType.uint64)
        winner = ScratchVar(TealType.uint64)
        challenger_play = ScratchVar(TealType.uint64)
        opponent_play = ScratchVar(TealType.uint64)
        return Seq(
            # basic sanity checks
            program.check_self(
                group_size=Int(1),
                group_index=Int(0),
            ),
            program.check_rekey_zero(1),
            Assert(
                And(
                    # verify accounts are opponents with each other
                    App.localGet(Txn.sender(), local_opponent) == Txn.accounts[1],
                    App.localGet(Txn.accounts[1], local_opponent) == Txn.sender(),
                    # verify same wager
                    App.localGet(Txn.sender(), local_wager) == App.localGet(Txn.accounts[1], local_wager),
                    # check commitment from challenger not empty
                    # this ensures that the sender is actually a challenger
                    App.localGet(Txn.sender(), local_commitment) != Bytes(""),
                    # check oppenent's reveal not empty
                    App.localGet(Txn.accounts[1], local_reveal) != Bytes(""),
                    # require reveal argument
                    Txn.application_args.length() == Int(2),
                    # check reveal is the same of the hashed commitment
                    Sha256(Txn.application_args[1]) == App.localGet(Txn.sender(), local_commitment),
                )
            ),
            wager.store(App.localGet(Txn.sender(), local_wager)),
            # store values of plays
            challenger_play.store(play_value(Txn.application_args[1])),
            opponent_play.store(play_value(App.localGet(Txn.accounts[1], local_reveal))),
            # check plays and send rewards
            winner.store(winner_account_index(challenger_play.load(), opponent_play.load())),
            If(challenger_play.load() == opponent_play.load())
            .Then(
                Seq(
                    # tie: refund wager to each party
                    send_reward(Int(0), wager.load()),
                    send_reward(Int(1), wager.load()),
                )
            )
            .Else(
                # send double wager to winner
                send_reward(winner.load(), wager.load() * Int(2))
            ),
            # reset contract after the outcome
            reset(Txn.sender()),
            reset(Txn.accounts[1]),
            Approve(),
        )

    return program.event(
        init=Approve(),
        opt_in=Seq(
            reset(Int(0)),
            Approve(),
        ),
        no_op=Seq(
            Cond(
                [
                    Txn.application_args[0] == op_challenge,
                    create_challenge(),
                ],
                [
                    Txn.application_args[0] == op_accept,
                    accept_challenge(),
                ],
                [
                    Txn.application_args[0] == op_reveal,
                    reveal(),
                ],
            ),
            Reject(),
        ),
    )


def clear():
    return Approve()
