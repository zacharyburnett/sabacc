#[macro_use]
extern crate impl_ops;

mod corellian_spike;
use corellian_spike::deck::Deck;

fn main() {
    let deck_1 = Deck::new();
    println!("{:?}", deck_1);
}
