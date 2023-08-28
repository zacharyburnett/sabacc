use rand::prelude::*;

#[derive(Debug)]
pub struct Deck {
    cards: Vec<super::card::Card>,
}

impl Deck {
    pub fn new() -> Self {
        let mut cards = Vec::with_capacity(60);

        cards.extend(vec![super::card::Card::sylop(); 2]);

        for suit in [
            super::card::Suit::Circle,
            super::card::Suit::Triangle,
            super::card::Suit::Square,
        ] {
            for value in -10..11 {
                if value != 0 {
                    cards.push(super::card::Card::new(suit.clone(), value))
                }
            }
        }

        Self { cards }
    }

    pub fn deal(&mut self, size: usize) -> Vec<super::card::Card> {
        self.cards.shuffle(&mut rand::thread_rng());

        let mut dealt = vec![];
        for index in 0..size {
            dealt.push(self.cards.swap_remove(index));
        }

        dealt
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_deck() {
        let deck = Deck::new();

        assert_eq!(deck.cards.len(), 62);
    }

    #[test]
    fn test_deal() {
        let mut deck = Deck::new();

        let dealt = deck.deal(2);

        assert_eq!(deck.cards.len(), 60);
        assert_eq!(dealt.len(), 2);

        assert_ne!(dealt[0], dealt[1]);
    }
}
