use std::collections::HashMap;

use super::card::Card;

#[derive(PartialOrd, PartialEq, Debug)]
pub enum Rank {
    // not zero
    Nulrhek,
    // zero
    Sabacc,
    // zero with a pair
    SabaccWithPair,
    // zero with two pairs
    RuleOfTwo,
    // zero with a three-of-a-kind
    BanthasWild,
    // zero with four cards in sequential order
    StraightKhyron,
    // zero with 1, 2, 3, 4 of the same sign, and a 10 of the opposite sign
    GeeWhiz,
    // zero with four of a kind
    Squadron,
    // zero with a same-sign three-of-a-kind and a pair of the opposite sign
    Rhylet,
    // zero with one Sylop and one pair
    YeeHaa,
    // zero with one Sylop and four of a kind (except 10s)
    Fleet,
    // zero with one Sylop and four 10s (two positive and two negative)
    FullSabacc,
    // zero with two Sylops
    PureSabacc,
}

#[derive(Clone, Debug)]
pub struct Hand {
    cards: Vec<Card>,
}

impl Hand {
    pub fn new(cards: Vec<Card>) -> Self {
        Hand { cards }
    }

    pub fn value(&self) -> i8 {
        self.cards.iter().fold(0, |sum, card| sum + card.value)
    }

    fn card_values(&self) -> Vec<i8> {
        let mut values = self
            .cards
            .iter()
            .map(|card| card.value)
            .collect::<Vec<i8>>();
        values.sort_unstable();
        values
    }

    // track value pairs, three-of-a-kinds, and four-of-a-kinds
    pub fn card_value_counts(&self) -> HashMap<i8, u8> {
        let values = self.card_values();
        let mut value_counts = HashMap::<i8, u8>::new();
        let mut index = 0;
        while index < values.len() {
            if !value_counts.contains_key(&values[index]) {
                value_counts.insert(values[index], 1);
            }
            for other_index in index + 1..values.len() {
                if values[other_index] == values[index] {
                    *value_counts.get_mut(&values[index]).unwrap() += 1;
                    index = other_index;
                } else {
                    break;
                }
            }
            index += 1;
        }
        value_counts
    }

    fn absolute_card_values(&self) -> Vec<u8> {
        let mut absolute_values = self
            .card_values()
            .iter()
            .map(|value| value.abs() as u8)
            .collect::<Vec<u8>>();
        absolute_values.sort_unstable();
        absolute_values
    }

    pub fn absolute_card_value_counts(&self) -> HashMap<u8, u8> {
        let mut absolute_value_counts = HashMap::<u8, u8>::new();
        for (value, count) in self.card_value_counts().iter() {
            let absolute_value = value.abs() as u8;
            if !absolute_value_counts.contains_key(&absolute_value) {
                absolute_value_counts.insert(absolute_value, *count);
            } else {
                *absolute_value_counts.get_mut(&absolute_value).unwrap() += count;
            }
        }
        absolute_value_counts
    }

    pub fn rank(&self) -> Rank {
        // only use values; rank in Corellian Spike does not care about suit
        let values = self.card_values();
        let absolute_values = self.absolute_card_values();

        let value_counts = self.card_value_counts();
        let absolute_value_counts = self.absolute_card_value_counts();

        let counts = value_counts.values().collect::<Vec<&u8>>();
        let absolute_counts = absolute_value_counts.values().collect::<Vec<&u8>>();

        // with zero value
        if self.value() == 0 {
            // special hands with certain sizes
            if values.len() == 2 {
                // with two sylops
                if value_counts[&0] == 2 {
                    return Rank::PureSabacc;
                }
            } else if values.len() == 3 {
                // with a sylop
                if values.contains(&0) {
                    // with a pair
                    if absolute_counts.contains(&&2) {
                        return Rank::YeeHaa;
                    }
                }
            } else if values.len() == 4 {
                // with a four-of-a-kind
                if absolute_counts.contains(&&4) {
                    return Rank::Squadron;
                } else {
                    // find a straight
                    let mut straight = true;
                    for index in 0..absolute_values.len() - 1 {
                        if absolute_values[index] + 1 != absolute_values[index + 1] {
                            straight = false;
                        }
                    }
                    // with a straight
                    if straight {
                        return Rank::StraightKhyron;
                    }
                }
            } else if values.len() == 5 {
                // with a sylop
                if values.contains(&0) {
                    // with a four-of-a-kind
                    if absolute_counts.contains(&&4) {
                        if absolute_value_counts.contains_key(&&10)
                            && absolute_value_counts[&10] == 4
                        {
                            return Rank::FullSabacc;
                        } else {
                            return Rank::Fleet;
                        }
                    }
                }
                // with a sign-sensitive three-of-a-kind
                if counts.contains(&&3) {
                    // with a sign-sensitive pair (necessarily of the opposite sign)
                    if counts.contains(&&2) {
                        return Rank::Rhylet;
                    }
                }
                // with 1, 2, 3, 4, and -10, or -1, -2, -3, -4, and 10
                if values == vec![-10, 1, 2, 3, 4] || values == vec![-4, -3, -2, -1, 10] {
                    return Rank::GeeWhiz;
                }
            }

            // with three-of-a-kind
            if absolute_counts.contains(&&3) {
                return Rank::BanthasWild;
            }

            // count pairs
            let mut pairs: u8 = 0;
            for count in absolute_counts {
                if count == &2 {
                    pairs += 1;
                }
            }

            // with two pairs
            if pairs == 2 {
                return Rank::RuleOfTwo;
            }

            // with one pair
            if pairs > 0 {
                return Rank::SabaccWithPair;
            }

            // otherwise, hand is a generic (not special) Sabacc
            return Rank::Sabacc;
        } else {
            // if the hand has a non-zero value, it is a Nulrhek
            return Rank::Nulrhek;
        }
    }
}

impl PartialEq for Hand {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == std::cmp::Ordering::Equal
    }
}

impl Eq for Hand {}

impl PartialOrd for Hand {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Hand {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let rank = self.rank();
        let other_rank = other.rank();

        if rank != other_rank {
            return Rank::partial_cmp(&rank, &other_rank).unwrap();
        } else if self.value() == other.value() {
            // special hand rules apply to compare the same rank and value
            if rank == Rank::Fleet || rank == Rank::Squadron {
                let four_of_a_kind_value: u8 = self
                    .absolute_card_value_counts()
                    .iter()
                    .map(|(value, count)| (*count, *value))
                    .collect::<HashMap<u8, u8>>()[&4];
                let other_four_of_a_kind_value: u8 = other
                    .absolute_card_value_counts()
                    .iter()
                    .map(|(value, count)| (*count, *value))
                    .collect::<HashMap<u8, u8>>()[&4];

                return u8::cmp(&other_four_of_a_kind_value, &four_of_a_kind_value);
            } else if rank == Rank::YeeHaa {
                let pair_value: u8 = self
                    .absolute_card_value_counts()
                    .iter()
                    .map(|(value, count)| (*count, *value))
                    .collect::<HashMap<u8, u8>>()[&2];
                let other_pair_value: u8 = other
                    .absolute_card_value_counts()
                    .iter()
                    .map(|(value, count)| (*count, *value))
                    .collect::<HashMap<u8, u8>>()[&2];

                return u8::cmp(&other_pair_value, &pair_value);
            } else if rank == Rank::Rhylet {
                let three_of_a_kind_value: i8 = self
                    .card_value_counts()
                    .iter()
                    .map(|(value, count)| (*count, *value))
                    .collect::<HashMap<u8, i8>>()[&3];
                let other_three_of_a_kind_value: i8 = other
                    .card_value_counts()
                    .iter()
                    .map(|(value, count)| (*count, *value))
                    .collect::<HashMap<u8, i8>>()[&3];

                return i8::cmp(
                    &other_three_of_a_kind_value.abs(),
                    &three_of_a_kind_value.abs(),
                );
            } else if rank == Rank::BanthasWild {
                let three_of_a_kind_value: u8 = self
                    .absolute_card_value_counts()
                    .iter()
                    .map(|(value, count)| (*count, *value))
                    .collect::<HashMap<u8, u8>>()[&3];
                let other_three_of_a_kind_value: u8 = other
                    .absolute_card_value_counts()
                    .iter()
                    .map(|(value, count)| (*count, *value))
                    .collect::<HashMap<u8, u8>>()[&3];

                return u8::cmp(&other_three_of_a_kind_value, &three_of_a_kind_value);
            } else if rank == Rank::StraightKhyron {
                let first_card = self.absolute_card_values()[0];
                let other_first_card = other.absolute_card_values()[0];

                return u8::cmp(&other_first_card, &first_card);
            } else if rank == Rank::RuleOfTwo {
                let mut lowest_pair_value: u8 = 11;
                for (value, count) in self.absolute_card_value_counts().iter() {
                    if count == &2 && value < &lowest_pair_value {
                        lowest_pair_value = *value;
                    }
                }

                let mut other_lowest_pair_value: u8 = 11;
                for (value, count) in other.absolute_card_value_counts().iter() {
                    if count == &2 && value < &other_lowest_pair_value {
                        other_lowest_pair_value = *value;
                    }
                }

                return u8::cmp(&other_lowest_pair_value, &lowest_pair_value);
            } else if rank == Rank::SabaccWithPair {
                let mut lowest_pair_value: u8 = 11;
                for (value, count) in self.absolute_card_value_counts().iter() {
                    if count >= &2 && value < &lowest_pair_value {
                        lowest_pair_value = *value;
                    }
                }

                let mut other_lowest_pair_value: u8 = 11;
                for (value, count) in other.absolute_card_value_counts().iter() {
                    if count >= &2 && value < &other_lowest_pair_value {
                        other_lowest_pair_value = *value;
                    }
                }

                return u8::cmp(&other_lowest_pair_value, &lowest_pair_value);
            } else if rank == Rank::Sabacc || rank == Rank::Nulrhek {
                // most cards wins
                if self.cards.len() != other.cards.len() {
                    return usize::cmp(&self.cards.len(), &other.cards.len());
                } else {
                    // higher sum of positive cards wins
                    let mut positive_card_sum: i8 = 0;
                    for value in self.card_values() {
                        if value > 0 {
                            positive_card_sum += value;
                        }
                    }
                    let mut other_positive_card_sum: i8 = 0;
                    for value in other.card_values() {
                        if value > 0 {
                            other_positive_card_sum += value;
                        }
                    }
                    if positive_card_sum != other_positive_card_sum {
                        return i8::cmp(&positive_card_sum, &other_positive_card_sum);
                    } else {
                        let mut highest_single_card_value: i8 = 0;
                        for value in self.card_values() {
                            if value > highest_single_card_value {
                                highest_single_card_value = value;
                            }
                        }

                        let mut other_highest_single_card_value: i8 = 0;
                        for value in other.card_values() {
                            if value > other_highest_single_card_value {
                                other_highest_single_card_value = value;
                            }
                        }

                        // higher-value single positive card wins
                        if highest_single_card_value != other_highest_single_card_value {
                            return i8::cmp(
                                &highest_single_card_value,
                                &other_highest_single_card_value,
                            );
                        }
                    }
                }
            }
        } else if self.value().abs() == other.value().abs() {
            // if both absolute values are equal, positive wins over negative
            return i8::cmp(&self.value(), &other.value());
        } else {
            // closer to zero wins
            return i8::cmp(&other.value().abs(), &self.value().abs());
        }

        return std::cmp::Ordering::Equal;
    }
}

#[cfg(test)]
mod tests {
    use rand::prelude::*;

    use super::super::card::{Card, Suit};
    use super::super::deck::Deck;
    use super::*;

    #[test]
    fn test_value() {
        let hand_1 = Hand::new(vec![
            Card::new(Suit::Triangle, 2),
            Card::new(Suit::Square, -4),
            Card::new(Suit::Square, 4),
        ]);

        let hand_2 = Hand::new(vec![
            Card::sylop(),
            Card::new(Suit::Square, -4),
            Card::new(Suit::Square, 4),
        ]);

        assert_eq!(hand_1.value(), 2);
        assert_eq!(hand_2.value(), 0);
    }

    #[test]
    fn test_deal() {
        let mut deck = Deck::new();

        let hand = Hand::new(deck.deal(2));

        assert_eq!(hand.cards.len(), 2);
    }

    #[test]
    fn test_equality() {
        let pure_sabacc = Hand::new(vec![Card::sylop(), Card::sylop()]);
        let full_sabacc = Hand::new(vec![
            Card::new(Suit::Circle, 10),
            Card::new(Suit::Triangle, 10),
            Card::sylop(),
            Card::new(Suit::Circle, -10),
            Card::new(Suit::Square, -10),
        ]);

        assert_eq!(pure_sabacc, pure_sabacc);
        assert_ne!(pure_sabacc, full_sabacc);
    }

    #[test]
    fn test_rank() {
        let pure_sabacc = Hand::new(vec![Card::sylop(), Card::sylop()]);
        let full_sabacc = Hand::new(vec![
            Card::new(Suit::Circle, 10),
            Card::new(Suit::Triangle, 10),
            Card::sylop(),
            Card::new(Suit::Circle, -10),
            Card::new(Suit::Square, -10),
        ]);
        let fleet_1 = Hand::new(vec![
            Card::new(Suit::Circle, -5),
            Card::new(Suit::Square, -5),
            Card::sylop(),
            Card::new(Suit::Circle, 5),
            Card::new(Suit::Square, 5),
        ]);
        let fleet_2 = Hand::new(vec![
            Card::new(Suit::Square, -6),
            Card::new(Suit::Circle, -6),
            Card::sylop(),
            Card::new(Suit::Circle, 6),
            Card::new(Suit::Triangle, 6),
        ]);
        let yee_haa_1 = Hand::new(vec![
            Card::new(Suit::Circle, 3),
            Card::sylop(),
            Card::new(Suit::Square, -3),
        ]);
        let yee_haa_2 = Hand::new(vec![
            Card::new(Suit::Circle, -6),
            Card::sylop(),
            Card::new(Suit::Circle, 6),
        ]);
        let rhylet_1 = Hand::new(vec![
            Card::new(Suit::Circle, 2),
            Card::new(Suit::Square, 2),
            Card::new(Suit::Triangle, 2),
            Card::new(Suit::Circle, -3),
            Card::new(Suit::Triangle, -3),
        ]);
        let rhylet_2 = Hand::new(vec![
            Card::new(Suit::Circle, 4),
            Card::new(Suit::Square, 4),
            Card::new(Suit::Triangle, 4),
            Card::new(Suit::Circle, -6),
            Card::new(Suit::Triangle, -6),
        ]);
        let squadron_1 = Hand::new(vec![
            Card::new(Suit::Square, -5),
            Card::new(Suit::Circle, -5),
            Card::new(Suit::Square, 5),
            Card::new(Suit::Circle, 5),
        ]);
        let squadron_2 = Hand::new(vec![
            Card::new(Suit::Square, -6),
            Card::new(Suit::Circle, -6),
            Card::new(Suit::Triangle, 6),
            Card::new(Suit::Circle, 6),
        ]);
        let gee_whiz_1 = Hand::new(vec![
            Card::new(Suit::Circle, 1),
            Card::new(Suit::Circle, 2),
            Card::new(Suit::Circle, 3),
            Card::new(Suit::Circle, 4),
            Card::new(Suit::Square, -10),
        ]);
        let gee_whiz_2 = Hand::new(vec![
            Card::new(Suit::Square, -1),
            Card::new(Suit::Square, -2),
            Card::new(Suit::Circle, -3),
            Card::new(Suit::Square, -4),
            Card::new(Suit::Circle, 10),
        ]);
        let straight_khyron_1 = Hand::new(vec![
            Card::new(Suit::Square, -6),
            Card::new(Suit::Circle, 7),
            Card::new(Suit::Circle, 8),
            Card::new(Suit::Square, -9),
        ]);
        let straight_khyron_2 = Hand::new(vec![
            Card::new(Suit::Circle, -7),
            Card::new(Suit::Circle, 8),
            Card::new(Suit::Square, 9),
            Card::new(Suit::Square, -10),
        ]);
        let banthas_wild_1 = Hand::new(vec![
            Card::new(Suit::Circle, 4),
            Card::new(Suit::Square, 4),
            Card::new(Suit::Triangle, 4),
            Card::new(Suit::Circle, -3),
            Card::new(Suit::Square, -9),
        ]);
        let banthas_wild_2 = Hand::new(vec![
            Card::new(Suit::Circle, 5),
            Card::new(Suit::Circle, -5),
            Card::new(Suit::Square, 5),
            Card::new(Suit::Square, -3),
            Card::new(Suit::Triangle, -2),
        ]);
        let rule_of_two_1 = Hand::new(vec![
            Card::new(Suit::Triangle, 3),
            Card::new(Suit::Circle, 3),
            Card::new(Suit::Circle, -5),
            Card::new(Suit::Square, 5),
            Card::new(Suit::Square, -6),
        ]);
        let rule_of_two_2 = Hand::new(vec![
            Card::new(Suit::Square, -9),
            Card::new(Suit::Square, 9),
            Card::new(Suit::Triangle, 4),
            Card::new(Suit::Square, -4),
        ]);
        let sabacc_with_pair_1 = Hand::new(vec![
            Card::new(Suit::Circle, 3),
            Card::new(Suit::Triangle, 3),
            Card::new(Suit::Square, -6),
        ]);
        let sabacc_with_pair_2 = Hand::new(vec![
            Card::new(Suit::Circle, 5),
            Card::new(Suit::Triangle, 5),
            Card::new(Suit::Square, -10),
        ]);
        let sabacc_1 = Hand::new(vec![
            Card::new(Suit::Circle, 8),
            Card::new(Suit::Circle, 1),
            Card::new(Suit::Circle, -9),
        ]);
        let sabacc_2 = Hand::new(vec![
            Card::new(Suit::Square, -9),
            Card::new(Suit::Circle, 5),
            Card::new(Suit::Square, 4),
        ]);
        let sabacc_3 = Hand::new(vec![
            Card::new(Suit::Triangle, -10),
            Card::new(Suit::Circle, 7),
            Card::new(Suit::Circle, 3),
        ]);
        let sabacc_4 = Hand::new(vec![
            Card::new(Suit::Square, -6),
            Card::new(Suit::Circle, 5),
            Card::new(Suit::Circle, 1),
        ]);
        let sabacc_5 = Hand::new(vec![
            Card::new(Suit::Square, -6),
            Card::new(Suit::Square, -4),
            Card::new(Suit::Circle, 7),
            Card::new(Suit::Circle, 3),
        ]);
        let sabacc_6 = Hand::new(vec![
            Card::new(Suit::Square, -6),
            Card::new(Suit::Circle, 5),
            Card::new(Suit::Circle, 1),
        ]);
        let nulrhek_1 = Hand::new(vec![
            Card::new(Suit::Square, 10),
            Card::new(Suit::Circle, 2),
            Card::new(Suit::Triangle, -4),
            Card::new(Suit::Triangle, -7),
        ]);
        let nulrhek_2 = Hand::new(vec![
            Card::new(Suit::Triangle, 9),
            Card::new(Suit::Circle, -5),
            Card::new(Suit::Triangle, 3),
            Card::new(Suit::Triangle, -6),
        ]);
        let nulrhek_3 = Hand::new(vec![
            Card::new(Suit::Circle, 9),
            Card::new(Suit::Circle, -6),
            Card::new(Suit::Circle, 4),
            Card::new(Suit::Square, -6),
        ]);
        let nulrhek_4 = Hand::new(vec![
            Card::new(Suit::Circle, 7),
            Card::new(Suit::Circle, -4),
            Card::new(Suit::Circle, 5),
            Card::new(Suit::Triangle, -7),
        ]);
        let nulrhek_5 = Hand::new(vec![
            Card::new(Suit::Triangle, 9),
            Card::new(Suit::Triangle, 4),
            Card::new(Suit::Triangle, -3),
            Card::new(Suit::Triangle, -1),
            Card::new(Suit::Circle, -8),
        ]);
        let nulrhek_6 = Hand::new(vec![
            Card::new(Suit::Circle, 10),
            Card::new(Suit::Circle, 5),
            Card::new(Suit::Square, -7),
            Card::new(Suit::Triangle, -7),
        ]);
        let nulrhek_7 = Hand::new(vec![
            Card::new(Suit::Circle, 3),
            Card::new(Suit::Circle, -2),
        ]);
        let nulrhek_8 = Hand::new(vec![
            Card::new(Suit::Square, -3),
            Card::new(Suit::Triangle, 2),
        ]);
        let nulrhek_9 = Hand::new(vec![
            Card::new(Suit::Triangle, 4),
            Card::new(Suit::Circle, -5),
        ]);
        let nulrhek_10 = Hand::new(vec![
            Card::new(Suit::Square, 5),
            Card::new(Suit::Circle, -1),
            Card::new(Suit::Circle, 3),
            Card::new(Suit::Square, -5),
        ]);

        // rank detection
        assert_eq!(pure_sabacc.rank(), Rank::PureSabacc);
        assert_eq!(full_sabacc.rank(), Rank::FullSabacc);
        assert_eq!(fleet_1.rank(), Rank::Fleet);
        assert_eq!(fleet_2.rank(), Rank::Fleet);
        assert_eq!(yee_haa_1.rank(), Rank::YeeHaa);
        assert_eq!(yee_haa_2.rank(), Rank::YeeHaa);
        assert_eq!(rhylet_1.rank(), Rank::Rhylet);
        assert_eq!(rhylet_2.rank(), Rank::Rhylet);
        assert_eq!(squadron_1.rank(), Rank::Squadron);
        assert_eq!(squadron_2.rank(), Rank::Squadron);
        assert_eq!(gee_whiz_1.rank(), Rank::GeeWhiz);
        assert_eq!(gee_whiz_2.rank(), Rank::GeeWhiz);
        assert_eq!(straight_khyron_1.rank(), Rank::StraightKhyron);
        assert_eq!(straight_khyron_2.rank(), Rank::StraightKhyron);
        assert_eq!(banthas_wild_1.rank(), Rank::BanthasWild);
        assert_eq!(banthas_wild_2.rank(), Rank::BanthasWild);
        assert_eq!(rule_of_two_1.rank(), Rank::RuleOfTwo);
        assert_eq!(rule_of_two_2.rank(), Rank::RuleOfTwo);
        assert_eq!(sabacc_with_pair_1.rank(), Rank::SabaccWithPair);
        assert_eq!(sabacc_with_pair_2.rank(), Rank::SabaccWithPair);
        assert_eq!(sabacc_1.rank(), Rank::Sabacc);
        assert_eq!(sabacc_2.rank(), Rank::Sabacc);
        assert_eq!(sabacc_3.rank(), Rank::Sabacc);
        assert_eq!(sabacc_4.rank(), Rank::Sabacc);
        assert_eq!(sabacc_5.rank(), Rank::Sabacc);
        assert_eq!(sabacc_6.rank(), Rank::Sabacc);
        assert_eq!(nulrhek_1.rank(), Rank::Nulrhek);
        assert_eq!(nulrhek_2.rank(), Rank::Nulrhek);
        assert_eq!(nulrhek_3.rank(), Rank::Nulrhek);
        assert_eq!(nulrhek_4.rank(), Rank::Nulrhek);
        assert_eq!(nulrhek_5.rank(), Rank::Nulrhek);
        assert_eq!(nulrhek_6.rank(), Rank::Nulrhek);
        assert_eq!(nulrhek_7.rank(), Rank::Nulrhek);
        assert_eq!(nulrhek_8.rank(), Rank::Nulrhek);
        assert_eq!(nulrhek_9.rank(), Rank::Nulrhek);
        assert_eq!(nulrhek_10.rank(), Rank::Nulrhek);

        // inter-rank ordering
        assert!(pure_sabacc > full_sabacc);
        assert!(full_sabacc > fleet_1);
        assert!(fleet_2 > yee_haa_1);
        assert!(yee_haa_2 > rhylet_1);
        assert!(rhylet_2 > squadron_1);
        assert!(squadron_2 > gee_whiz_1);
        assert!(gee_whiz_2 > straight_khyron_1);
        assert!(straight_khyron_2 > banthas_wild_1);
        assert!(banthas_wild_2 > rule_of_two_1);
        assert!(rule_of_two_2 > sabacc_with_pair_1);
        assert!(sabacc_with_pair_2 > sabacc_1);
        assert!(sabacc_2 > nulrhek_1);

        assert!(pure_sabacc > nulrhek_1);

        // intra-rank ordering
        assert!(fleet_1 > fleet_2);
        assert!(yee_haa_1 > yee_haa_2);
        assert!(rhylet_1 > rhylet_2);
        assert!(gee_whiz_1 == gee_whiz_2);
        assert!(straight_khyron_1 > straight_khyron_2);
        assert!(banthas_wild_1 > banthas_wild_2);
        assert!(rule_of_two_1 > rule_of_two_2);
        assert!(sabacc_with_pair_1 > sabacc_with_pair_2);
        assert!(sabacc_1 > sabacc_2);
        assert!(sabacc_2 < sabacc_3);
        assert!(sabacc_3 > sabacc_4);
        assert!(sabacc_4 < sabacc_5);
        assert!(sabacc_5 > sabacc_6);
        assert!(sabacc_6 > nulrhek_1);
        assert!(nulrhek_1 > nulrhek_2);
        assert!(nulrhek_2 < nulrhek_3);
        assert!(nulrhek_3 > nulrhek_4);
        assert!(nulrhek_4 < nulrhek_5);
        assert!(nulrhek_5 > nulrhek_6);
        assert!(nulrhek_6 > nulrhek_7);
        assert!(nulrhek_7 > nulrhek_8);
        assert!(nulrhek_8 < nulrhek_9);
        assert!(nulrhek_9 > nulrhek_10);

        // hand sorting
        let reference_hands = vec![
            pure_sabacc,
            full_sabacc,
            fleet_1,
            fleet_2,
            yee_haa_1,
            yee_haa_2,
            rhylet_1,
            rhylet_2,
            gee_whiz_1,
            gee_whiz_2,
            straight_khyron_1,
            straight_khyron_2,
            banthas_wild_1,
            banthas_wild_2,
            rule_of_two_1,
            rule_of_two_2,
            sabacc_with_pair_1,
            sabacc_with_pair_2,
            sabacc_1,
            sabacc_2,
            sabacc_6,
            nulrhek_1,
            nulrhek_2,
            nulrhek_4,
        ];

        let mut hands = reference_hands.clone();
        hands.shuffle(&mut rand::thread_rng());

        hands.sort_unstable();
        hands.reverse();

        assert_eq!(hands, reference_hands);
    }
}
