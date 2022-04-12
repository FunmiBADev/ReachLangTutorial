'reach 0.1'

const [isHand, ROCK, PAPER, SCISSORS] = makeEnum(3)
const [isOutcome, D_WINS, DRAW, F_WINS] = makeEnum(3)

const winner = (handFunmi, handDemi) => (handFunmi + (4 - handDemi)) % 3

assert(winner(ROCK, PAPER) == D_WINS)
assert(winner(PAPER, ROCK) == F_WINS)
assert(winner(ROCK, ROCK) == DRAW)

forall(UInt, handFunmi =>
  forall(UInt, handDemi => assert(isOutcome(winner(handFunmi, handDemi))))
)

forall(UInt, hand => assert(winner(hand, hand) == DRAW))

const Player = {
  ...hasRandom,
  getHand: Fun([], UInt),
  seeOutcome: Fun([UInt], Null),
  informTimeout: Fun([], Null)
}

export const main = Reach.App(() => {
  const Funmi = Participant('Funmi', {
    ...Player,
    wager: UInt, // atomic units of currency
    deadline: UInt // time delta (blocks/rounds)
  })
  const Demi = Participant('Demi', {
    ...Player,
    acceptWager: Fun([UInt], Null)
  })
  init()

  const informTimeout = () => {
    each([Funmi, Demi], () => {
      interact.informTimeout()
    })
  }

  Funmi.only(() => {
    const wager = declassify(interact.wager)
    const deadline = declassify(interact.deadline)
  })
  Funmi.publish(wager, deadline).pay(wager)
  commit()

  Demi.only(() => {
    interact.acceptWager(wager)
  })
  Demi.pay(wager).timeout(relativeTime(deadline), () =>
    closeTo(Funmi, informTimeout)
  )

  var outcome = DRAW
  invariant(balance() == 2 * wager && isOutcome(outcome))
  while (outcome == DRAW) {
    commit()

    Funmi.only(() => {
      const _handFunmi = interact.getHand()
      const [_commitFunmi, _saltFunmi] = makeCommitment(interact, _handFunmi)
      const commitFunmi = declassify(_commitFunmi)
    })
    Funmi.publish(commitFunmi).timeout(relativeTime(deadline), () =>
      closeTo(Demi, informTimeout)
    )
    commit()

    unknowable(Demi, Funmi(_handFunmi, _saltFunmi))
    Demi.only(() => {
      const handDemi = declassify(interact.getHand())
    })
    Demi.publish(handDemi).timeout(relativeTime(deadline), () =>
      closeTo(Funmi, informTimeout)
    )
    commit()

    Funmi.only(() => {
      const saltFunmi = declassify(_saltFunmi)
      const handFunmi = declassify(_handFunmi)
    })
    Funmi.publish(saltFunmi, handFunmi).timeout(relativeTime(deadline), () =>
      closeTo(Demi, informTimeout)
    )
    checkCommitment(commitFunmi, saltFunmi, handFunmi)

    outcome = winner(handFunmi, handDemi)
    continue
  }

  assert(outcome == F_WINS || outcome == D_WINS)
  transfer(2 * wager).to(outcome == F_WINS ? Funmi : Demi)
  commit()

  each([Funmi, Demi], () => {
    interact.seeOutcome(outcome)
  })
})
