import { loadStdlib } from '@reach-sh/stdlib'
import * as backend from './build/index.main.mjs'

const stdlib = loadStdlib()

const startingBalance = stdlib.parseCurrency(100)
const accAlice = await stdlib.newTestAccount(startingBalance)
const accBob = await stdlib.newTestAccount(startingBalance)

const fmt = x => stdlib.formatCurrency(x, 4)
const getBalance = async who => fmt(await stdlib.balanceOf(who))
const beforeAlice = await getBalance(accAlice)
const beforeBob = await getBalance(accBob)

const ctcAlice = accAlice.contract(backend)
const ctcBob = accBob.contract(backend, ctcAlice.getInfo())

const HAND = ['Rock', 'Paper', 'Scissors']
const OUTCOME = ['Bob wins!', 'Draw', 'Alice wins!']

const Player = who => ({
  ...stdlib.hasRandom,
  getHand: () => {
    const hand = Math.floor(Math.random() * 3)
    console.log(`${who} played ${HAND[hand]}`)
    return hand
  },
  seeOutcome: outcome => {
    console.log(`${who} saw outcome ${OUTCOME[outcome]}`)
  },
  informTimeout: () => {
    console.log(`${who} observed a timeout`)
  }
})

await Promise.all([
  ctcAlice.p.Alice({
    // implement Alice's interact object here
    ...Player('Alice'),
    wager: stdlib.parseCurrency(5),
    deadline: 10
  }),
  ctcBob.p.Bob({
    // implement Bob's interact object here
    ...Player('Bob'),
    acceptWager: async amt => {
      if (Math.random() <= 0.5) {
        for (let i = 0; i < 10; i++) {
          console.log(` Bob takes his sweet time...`)
          await stdlib.wait(1)
        }
      } else {
        console.log(`Bob accepts the wager of ${fmt(amt)}`)
      }
    }
  })
])

const afterAlice = await getBalance(accAlice)
const afterBob = await getBalance(accBob)

console.log(`Alice went from ${beforeAlice} to ${afterAlice}.`)
console.log(`Bob went from ${beforeBob} to ${afterBob}.`)
