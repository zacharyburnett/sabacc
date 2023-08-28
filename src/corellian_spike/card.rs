use core::panic;
use std::ops;

#[derive(Clone, Debug, PartialEq)]
pub enum Suit {
    Sylop,
    Circle,
    Triangle,
    Square,
}

#[derive(Clone, Debug)]
pub struct Card {
    pub suit: Suit,
    pub value: i8,
}

impl Card {
    pub fn new(suit: Suit, value: i8) -> Self {
        if suit == Suit::Sylop && value != 0 {
            panic!("invalid value {} for sylop; must have a value of 0", value)
        } else if suit != Suit::Sylop && (value == 0 || value < -10 || value > 10) {
            panic!(
                "invalid value {} for suit {:?}; must have a positive or negative value between 1 and 10",
                value, suit
            )
        }

        Self { suit, value }
    }

    pub fn sylop() -> Self {
        Self::new(Suit::Sylop, 0)
    }
}

impl_op_ex!(+ |a: &Card, b: &Card| -> i8 { a.value + b.value });
impl_op_ex!(-|a: &Card, b: &Card| -> i8 { a.value - b.value });

impl PartialEq for Card {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

impl Eq for Card {}

impl PartialOrd for Card {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Card {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        i8::cmp(&self.value, &other.value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_construction() {
        let card_1 = Card::new(Suit::Circle, 3);
        let card_2 = Card::new(Suit::Triangle, -10);
        let card_3 = Card::sylop();
    }

    #[test]
    fn test_addition() {
        let card_1 = Card::new(Suit::Circle, 3);
        let card_2 = Card::new(Suit::Triangle, -10);
        let card_3 = Card::sylop();

        assert_eq!(&card_1 + &card_2, -7);
        assert_eq!(&card_2 + &card_3, -10);
        assert_eq!(&card_1 + &card_3, 3);
    }
}
