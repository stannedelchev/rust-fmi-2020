const FIZZ: &str = "Fizz";
const BUZZ: &str = "Buzz";
const FIZZ_BUZZ: &str = "Fizzbuzz";

/// Вход: променлива `n`, която описва броя елементи, които ще генерираме в резултата.
///
/// За всяко число от 1 до `n` включително, искаме съответстващия елемент в резултата да е:
///
/// - String със съдържание "Fizz" ако числото се дели на 3, но не на 5
/// - String със съдържание "Buzz" ако числото се дели на 5, но не на 3
/// - String със съдържание "Fizzbuzz" ако числото се дели и на 3, и на 5
/// - Числото конвертирано до низ, във всички други случаи
///
/// Тоест, във `fizzbuzz(3)`, първия елемент ще бъде `String::from("1")`, втория
/// `String::from("2")`, последния `String::from("Fizz")`.
///
/// Ако `n` е 0, очакваме празен вектор за резултат.
///
pub fn fizzbuzz(n: usize) -> Vec<String> {
    custom_buzz(n, 3, 5)
}

/// Вход:
/// - променлива `n`, която описва броя елементи, които ще генерираме в резултата.
/// - променливи `k1` и `k2`, които са двата делителя, които ще използваме за заместване.
///
/// За всяко число от 1 до `n` включително, искаме съответстващия елемент в резултата да е:
///
/// - String със съдържание "Fizz" ако числото се дели на k1, но не на k2
/// - String със съдържание "Buzz" ако числото се дели на k2, но не на k1
/// - String със съдържание "Fizzbuzz" ако числото се дели и на k1, и на k2
/// - Числото конвертирано до низ, във всички други случаи
///
/// Ако `n` е 0, очакваме празен вектор за резултат.
/// Ако `k1` или `k2` са 0 или 1, очакваме функцията да panic-не с каквото съобщение изберете.
///
pub fn custom_buzz(n: usize, k1: u8, k2: u8) -> Vec<String> {
    let k1 = k1 as usize;
    let k2 = k2 as usize;

    if k1 <= 1 || k2 <= 1 {
        panic!("k1 and k2 should be larger than 1");
    }

    (1..=n)
        .map(|i| match i {
            i if i % k1 == 0 && i % k2 == 0 => FIZZ_BUZZ.to_string(),
            i if i % k1 == 0 => FIZZ.to_string(),
            i if i % k2 == 0 => BUZZ.to_string(),
            _ => i.to_string(),
        })
        .collect()
}

/// Параметри:
/// - полета `k1` и `k2`, които са двата делителя, които ще използваме за заместване.
/// - поле `labels`, които са трите етикета, които съответстват на коефициентите
///
pub struct FizzBuzzer {
    pub k1: u8,
    pub k2: u8,
    pub labels: [String; 3],
}

impl FizzBuzzer {
    /// За всяко число от 1 до `n` включително, искаме съответстващия елемент в резултата да е:
    ///
    /// - Първия String от полето `labels` ако числото се дели на k1, но не на k2
    /// - Втория String от полето `labels` ако числото се дели на k2, но не на k1
    /// - Третия String от полето `labels` ако числото се дели и на k1, и на k2
    /// - Числото конвертирано до низ, във всички други случаи
    ///
    /// Ако `n` е 0, очакваме празен вектор за резултат.
    /// Ако `k1` или `k2` са 0 или 1, очакваме функцията да panic-не с каквото съобщение изберете.
    ///
    pub fn take(&self, n: usize) -> Vec<String> {
        let k1 = self.k1 as usize;
        let k2 = self.k2 as usize;
        let k1_label = &self.labels[0];
        let k2_label = &self.labels[1];
        let k1k2_label = &self.labels[2];

        if k1 <= 1 || k2 <= 1 {
            panic!("k1 and k2 should be larger than 1");
        }

        (1..=n)
            .map(|i| match i {
                i if i % k1 == 0 && i % k2 == 0 => k1k2_label.clone(),
                i if i % k1 == 0 => k1_label.clone(),
                i if i % k2 == 0 => k2_label.clone(),
                _ => i.to_string(),
            })
            .collect()
    }

    /// Параметъра `index` указва кой етикет от полето `labels` променяме, от 0 до 2. Ако подадения
    /// `index` е извън тези рамки, очакваме функцията да panic-не.
    ///
    /// Стойността `value` е низа, който ще сложим на този индекс в полето `labels`.
    ///
    pub fn change_label(&mut self, index: usize, value: &String) {
        self.labels[index] = value.clone();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn expected_20_nums() -> Vec<String> {
        [
            "1", "2", FIZZ, "4", BUZZ, FIZZ, "7", "8", FIZZ, BUZZ, "11", FIZZ, "13", "14",
            FIZZ_BUZZ, "16", "17", FIZZ, "19", BUZZ,
        ]
        .iter()
        .map(|x| x.to_string())
        .collect()
    }

    mod fizzbuzz {
        use super::fizzbuzz;
        #[test]
        fn n_0_returns_empty_vec() {
            assert_eq!(fizzbuzz(0), Vec::<String>::new())
        }

        #[test]
        fn n_20_returns_correct_results() {
            let expected = super::expected_20_nums();
            assert_eq!(fizzbuzz(20), expected)
        }
    }

    mod custom_buzz {
        use super::custom_buzz;

        #[test]
        fn n_0_retuns_empty_vec() {
            assert_eq!(custom_buzz(0, 3, 5), Vec::<String>::new())
        }

        #[should_panic]
        #[test]
        fn k1_is_0_panics() {
            custom_buzz(1, 0, 5);
        }

        #[should_panic]
        #[test]
        fn k1_is_1_panics() {
            custom_buzz(1, 1, 5);
        }
        #[should_panic]
        #[test]
        fn k2_is_0_panics() {
            custom_buzz(1, 3, 0);
        }

        #[should_panic]
        #[test]
        fn k2_is_1_panics() {
            custom_buzz(1, 3, 1);
        }

        #[test]
        fn n_20_returns_correct_results() {
            let expected = super::expected_20_nums();
            assert_eq!(custom_buzz(20, 3, 5), expected)
        }
    }

    mod fizbuzzer {
        use super::FizzBuzzer;
        fn make_default_labels() -> [String; 3] {
            [
                super::FIZZ.to_string(),
                super::BUZZ.to_string(),
                super::FIZZ_BUZZ.to_string(),
            ]
        }

        #[test]
        fn n_0_retuns_empty_vec() {
            let sut = FizzBuzzer {
                k1: 3,
                k2: 5,
                labels: make_default_labels(),
            };
            let actual = sut.take(0);
            assert_eq!(actual, Vec::<String>::new())
        }

        #[should_panic]
        #[test]
        fn k1_is_0_panics() {
            let sut = FizzBuzzer {
                k1: 0,
                k2: 5,
                labels: make_default_labels(),
            };
            sut.take(20);
            assert!(true);
        }

        #[should_panic]
        #[test]
        fn k1_is_1_panics() {
            let sut = FizzBuzzer {
                k1: 1,
                k2: 5,
                labels: make_default_labels(),
            };
            sut.take(20);
            assert!(true);
        }

        #[should_panic]
        #[test]
        fn k2_is_0_panics() {
            let sut = FizzBuzzer {
                k1: 3,
                k2: 0,
                labels: make_default_labels(),
            };
            sut.take(20);
            assert!(true);
        }

        #[should_panic]
        #[test]
        fn k2_is_1_panics() {
            let sut = FizzBuzzer {
                k1: 3,
                k2: 1,
                labels: make_default_labels(),
            };
            sut.take(20);
            assert!(true);
        }

        #[test]
        fn n_20_returns_correct_results() {
            let expected = super::expected_20_nums();
            let sut = FizzBuzzer {
                k1: 3,
                k2: 5,
                labels: make_default_labels(),
            };
            let actual = sut.take(20);
            assert_eq!(actual, expected);
        }

        #[should_panic]
        #[test]
        fn change_label_out_of_bounds_panics() {
            let mut sut = FizzBuzzer {
                k1: 3,
                k2: 5,
                labels: make_default_labels(),
            };
            let out_of_bounds_index = sut.labels.len() + 1;
            sut.change_label(out_of_bounds_index, &"test".to_string());
        }

        #[test]
        fn change_label_and_take_20_returns_correct_results() {
            let expected: Vec<String> = super::expected_20_nums()
                .iter()
                .map(|s| match s.as_str() {
                    super::FIZZ => "F".to_string(),
                    super::BUZZ => "B".to_string(),
                    super::FIZZ_BUZZ => "FB".to_string(),
                    s => s.to_string(),
                })
                .collect();
            let mut sut = FizzBuzzer {
                k1: 3,
                k2: 5,
                labels: make_default_labels(),
            };
            sut.change_label(0, &"F".to_string());
            sut.change_label(1, &"B".to_string());
            sut.change_label(2, &"FB".to_string());
            let actual = sut.take(20);
            assert_eq!(actual, expected);
        }

        #[te]
    }
}
