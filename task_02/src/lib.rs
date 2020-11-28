#[derive(Debug, PartialEq, Eq)]
pub struct Bigint {
    sign: i8,
    digits: Vec<u8>,
}

impl Bigint {
    /// Конструира нов Bigint със стойност "0" и положителен знак.
    /// Това може да означава празен вектор с цифри или масив с една цифра `0` -- ваш избор.
    ///
    pub fn new() -> Self {
        Bigint::from_components(vec![], 1)
    }

    /// Конструира нов Bigint с подадените цифри и знак.
    ///
    /// Тук е добро място където можете да вкарате малко валидация и нормализиране на входа -- да
    /// премахнете допълнителни нули или да се погрижите, че нулата винаги има консистентен знак.
    /// Стига да се погрижите винаги да използвате функцията при конструириане на нови Bigint-ове.
    ///
    /// Тази функция НЕ Е публична, така че НЕ Е задължителна -- ако не ви трябва, може смело да я
    /// изтриете.
    ///
    fn from_components(digits: Vec<u8>, sign: i8) -> Self {
        Bigint { digits, sign }
    }

    /// Връща `true` ако числото е положително. Нулата не е положителна.
    pub fn is_positive(&self) -> bool {
        self.sign == 1 && !self.is_zero()
    }

    /// Връща `true` ако числото е отрицателно. Нулата не е отрицателна.
    pub fn is_negative(&self) -> bool {
        self.sign == -1 && !self.is_zero()
    }

    fn is_zero(&self) -> bool {
        self.digits.is_empty()
    }

    fn add_same_sign(&self, other: &Bigint) -> Option<Bigint> {
        if self.sign != other.sign {
            return None;
        }

        let larger_digits = std::cmp::max(&self.digits, &other.digits);
        let shorter_digits = std::cmp::min(&self.digits, &other.digits);
        let mut result = larger_digits.clone();
        result.reverse();
        result.push(0);

        let mut carry;
        for i in 0..shorter_digits.len() {
            let left = result[i];
            let right = shorter_digits[shorter_digits.len() - 1 - i];
            let sum = left + right;
            carry = sum / 10;
            result[i] = sum % 10;

            for j in (i + 1)..result.len() {
                result[j] += carry;

                if result[j] < 10 {
                    break;
                } else if result[j] == 10 {
                    result[j] = 0;
                }
            }
        }

        result.reverse();
        result = result.into_iter().skip_while(|i| *i == 0).collect();
        Some(Bigint::from_components(result, self.sign))
    }

    fn add_diff_sign(&self, other: &Bigint) -> Option<Bigint> {
        if self.sign == other.sign {
            return None;
        }

        if &self.invert() == other {
            return Some(Bigint::new());
        }

        let (larger, smaller) = self.abs_max(other);

        let mut result = larger.digits.clone();
        let smaller_len = smaller.digits.len();
        let larger_smaller_len_diff = larger.digits.len() - smaller_len;
        for i in (0..smaller_len).rev() {
            let offset_in_larger = i + larger_smaller_len_diff;
            let minuend = result[offset_in_larger];
            let subtrahend = smaller.digits[i];

            if minuend >= subtrahend {
                result[offset_in_larger] = minuend - subtrahend;
            } else {
                result[offset_in_larger] = 10 + minuend - subtrahend;

                for j in (0..offset_in_larger).rev() {
                    if result[j] == 0 {
                        result[j] = 9;
                    } else {
                        result[j] -= 1;
                        break;
                    }
                }
            }
        }

        Some(Bigint::from_components(
            result.into_iter().skip_while(|&i| i == 0).collect(),
            larger.sign,
        ))
    }

    fn abs(&self) -> Bigint {
        Bigint::from_components(self.digits.clone(), 1)
    }

    fn invert(&self) -> Bigint {
        Bigint::from_components(self.digits.clone(), self.sign * -1)
    }

    fn abs_max<'a>(&'a self, other: &'a Bigint) -> (&'a Bigint, &'a Bigint) {
        let self_abs = self.abs();
        let other_abs = other.abs();

        let abs_larger = std::cmp::max(&self_abs, &other_abs);
        match abs_larger {
            abs_larger if abs_larger == &self_abs => (&self, &other),
            abs_larger if abs_larger == &other_abs => (&other, &self),
            _ => unreachable!(),
        }
    }
}

use std::str::FromStr;

#[derive(Debug)]
pub struct ParseError;

impl FromStr for Bigint {
    type Err = ParseError;

    /// Очакваме низа да е във формат десетично цяло число с опционален знак, тоест всички тези
    /// неща би трябвало да върнат `Ok` резултат с конструиран Bigint:
    ///
    /// #    Bigint::from_str("123") // => положителен знак по подразбиране
    /// #    Bigint::from_str("+123")
    /// #    Bigint::from_str("-123")
    ///
    /// Това включва нулата, като имате предвид че, както казахме, +0 и -0 трябва да са
    /// еквивалентни.
    ///
    /// Ако подадения низ е празен, това връща същото като да сме подали "0". Ако подадения низ е
    /// само "+" или "-", ваше решение е дали да е нула или да е грешка, няма да го тестваме.
    ///
    /// Ако подадения низ започва с нули, това няма значение -- игнорират се. Тоест, конструиране с
    /// "00123" ще е същото като конструиране с "123".
    ///
    /// Ако сме подали низ, който включва каквито и да е други символи освен цифрите 0-9 (и
    /// опционален начален знак), очакваме да върнете `ParseError`.
    ///
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut result: Vec<u8> = vec![];

        if s.is_empty() {
            return Ok(Bigint::new());
        }

        let mut sign: Option<i8> = None;
        let mut filter_prefix_zeroes = true;

        for c in s.chars() {
            match c {
                '+' if sign == None => sign = Some(1),
                '-' if sign == None => sign = Some(-1),
                '0' if sign == None => sign = Some(1),
                '0'..='9' if sign == None => {
                    sign = Some(1);
                    result.push(c.to_digit(10).unwrap() as u8);
                    filter_prefix_zeroes = false;
                }
                '0'..='9' => match c.to_digit(10) {
                    None => return Err(ParseError),
                    Some(digit) if digit == 0 && filter_prefix_zeroes => continue,
                    Some(digit) => {
                        result.push(digit as u8);
                        filter_prefix_zeroes = false;
                    }
                },
                _ => return Err(ParseError),
            }
        }

        Ok(Bigint::from_components(result, sign.unwrap()))
    }
}

use std::cmp::Ordering;

impl PartialOrd for Bigint {
    /// Две цели числа винаги могат да се сравнят, така че "частичното" равенство е същото като
    /// пълното.
    ///
    fn partial_cmp(&self, other: &Bigint) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Bigint {
    /// Ако едното от числата е положително, а другото -- отрицателно, положителното е по-голямо.
    ///
    /// Ако едното от числата има по-голям брой цифри, то ще бъде по-голямото. (Стига да не са нули
    /// -- вероятно е добра идея да се погрижите да няма започващи нули при конструкция.)
    ///
    /// Ако двете числа имат еднакъв брой цифри, лексикографско сравнение на числата ще ви даде
    /// правилен резултат -- от по-значимите цифри към по-малко значимите. Внимавайте в какъв ред
    /// си държите цифритe и дали не трябва да ги обърнете.
    ///
    /// Ако двете числа са отрицателни, сравнението по абсолютна стойност ще е обърнато (-1 е
    /// по-голямо от -2) -- погледнете документацията на `Ordering` за това как лесно можете да
    /// обърнете резултата.
    ///
    fn cmp(&self, other: &Bigint) -> Ordering {
        if self.is_positive() && other.is_negative() {
            return Ordering::Greater;
        }

        if self.is_negative() && other.is_positive() {
            return Ordering::Less;
        }

        if self.is_zero() && other.is_zero() {
            return Ordering::Equal;
        }

        if self.digits.len() > other.digits.len() && self.is_negative() {
            return Ordering::Less;
        }

        if self.digits.len() > other.digits.len() && self.is_positive() {
            return Ordering::Greater;
        }

        if self.digits.len() < other.digits.len() && self.is_negative() {
            return Ordering::Greater;
        }

        if self.digits.len() < other.digits.len() && self.is_positive() {
            return Ordering::Less;
        }

        if self.is_positive() {
            self.digits.cmp(&other.digits)
        } else {
            self.digits.cmp(&other.digits).reverse()
        }
    }
}

use std::ops::{Add, Sub};

impl Add for Bigint {
    type Output = Bigint;

    /// За да съберете две числа, първия въпрос е: какви са им знаците?
    ///
    /// - Ако и двете са положителни, събираме ги цифра по цифра и слагаме на резултата положителен
    ///   знак.
    /// - Ако и двете са отрицателни, пак можем да ги съберем цифра по цифра и да сложим
    ///   отрицателен знак на крайния резултат.
    /// - Ако имат различни знаци, намираме по-голямото *по абсолютна стойност*. Изваждаме цифрите
    ///   на по-малкото от по-голямото. Знака на резултата е знака на по-голямото по абсолютна
    ///   стойност. Ако са равни, резултата трябва да е нула (която винаги се очаква да е
    ///   положителна).
    ///
    /// При събиране цифра по цифра, не забравяйте да пренасяте "едно наум" ако резултата е
    /// по-голям от десетична цифра. При различна дължина на списъците от цифри, можете да
    /// запълните с нули, да внимавате с индексите, или нещо по средата.
    ///
    fn add(self, other: Self) -> Self {
        if self.is_zero() && other.is_zero() {
            return Bigint::new();
        }

        if let Some(result) = self.add_same_sign(&other) {
            return result;
        }

        if let Some(result) = self.add_diff_sign(&other) {
            return result;
        }

        unreachable!()
    }
}

impl Sub for Bigint {
    type Output = Bigint;

    /// Изваждането често се имплементира като събиране с отрицателен знак. Тоест, `A - B` е
    /// еквивалентно на `A + (-B)`. Можете да имплементирате изваждането като форма на събиране, и
    /// в него да пакетирате логиката. Или можете да проверите знаците и да разделите логиката по
    /// събиране и по изваждане между `add` и `sub`.
    ///
    /// При изваждане, също не забравяйте "едното наум", ако цифрата от която вадите е по-малката,
    /// което ще се преведе до едно "-1" на следващата цифра. Погрижете се винаги да вадите от
    /// по-голямото по абсолютна стойност число, и после сложете какъвто знак се налага.
    ///
    /// Внимавайте с типовете -- изваждане на unsigned от unsigned число може да се счупи.
    ///
    fn sub(self, other: Self) -> Self {
        self + other.invert()
    }
}

#[cfg(test)]
mod tests {
    mod new {
        use crate::Bigint;

        #[test]
        fn positive_zero_equals_negative_zero() {
            let positive_zero = Bigint::new();
            let mut negative_zero = Bigint::new();
            negative_zero.sign = 1;

            assert_eq!(positive_zero, negative_zero);
        }

        #[test]
        fn zero_is_not_positive() {
            assert_eq!(false, Bigint::new().is_positive())
        }

        #[test]
        fn zero_is_not_negative() {
            assert_eq!(false, Bigint::new().is_negative())
        }

        #[test]
        fn zero_is_zero() {
            assert!(Bigint::from_components(vec![], 1).is_zero())
        }

        #[test]
        fn new_is_zero() {
            assert!(Bigint::new().is_zero())
        }

        #[test]
        fn _123_is_not_zero() {
            assert_eq!(false, Bigint::from_components(vec![1, 2, 3], 1).is_zero())
        }

        #[test]
        fn minus123_is_negative() {
            let sut = Bigint::from_components(vec![1, 2, 3], -1);
            assert!(sut.is_negative())
        }

        #[test]
        fn plus123_is_positive() {
            let sut = Bigint::from_components(vec![1, 2, 3], 1);
            assert!(sut.is_positive())
        }
    }

    mod from_str {
        use crate::Bigint;
        use std::str::FromStr;

        #[test]
        fn from_str_plus_zero_is_zero() {
            assert!(true, Bigint::from_str("+0").unwrap().is_zero())
        }

        #[test]
        fn from_str_minus_zero_is_zero() {
            assert!(true, Bigint::from_str("-0").unwrap().is_zero())
        }

        #[test]
        fn from_str_zero_is_zero() {
            assert!(true, Bigint::from_str("0").unwrap().is_zero())
        }

        #[test]
        fn from_str_plus_many_zeroes_is_zero() {
            assert!(Bigint::from_str("+000000000").unwrap().is_zero())
        }

        #[test]
        fn from_str_123() {
            let sut = Bigint::from_str("123").unwrap();
            assert_eq!(1, sut.sign);
            assert_eq!(vec![1, 2, 3], sut.digits);
        }

        #[test]
        fn from_str_plus123() {
            let sut = Bigint::from_str("+123").unwrap();
            assert_eq!(1, sut.sign);
            assert_eq!(vec![1, 2, 3], sut.digits);
        }

        #[test]
        fn from_str_minus123() {
            let sut = Bigint::from_str("-123").unwrap();
            assert_eq!(-1, sut.sign);
            assert_eq!(vec![1, 2, 3], sut.digits);
        }

        #[test]
        fn from_str_plus000000100001() {
            let sut = Bigint::from_str("+000000100001").unwrap();
            assert_eq!(1, sut.sign);
            assert_eq!(vec![1, 0, 0, 0, 0, 1], sut.digits);
        }

        #[test]
        fn from_str_plus00000s000001() {
            let sut = Bigint::from_str("+00000s000001");
            assert!(sut.is_err());
        }

        #[test]
        fn from_str_5000() {
            let sut = Bigint::from_str("5000").unwrap();
            assert_eq!(1, sut.sign);
            assert_eq!(vec![5, 0, 0, 0], sut.digits);
        }

        #[test]
        fn from_str_a123_returns_error() {
            let sut = Bigint::from_str("a123");
            assert!(sut.is_err());
        }

        #[test]
        fn from_str_plus_a123_returns_error() {
            let sut = Bigint::from_str("+a123");
            assert!(sut.is_err());
        }

        #[test]
        fn from_str_space123_returns_error() {
            let sut = Bigint::from_str(" 123");
            assert!(sut.is_err());
        }

        #[test]
        fn from_str_empty_str() {
            let sut = Bigint::from_str("").unwrap();
            assert_eq!(true, sut.is_zero());
            assert_eq!(1, sut.sign);
            assert_eq!(Vec::<u8>::new(), sut.digits);
        }
    }

    mod cmp {
        use crate::Bigint;
        use std::cmp::Ordering;
        use std::str::FromStr;

        #[test]
        fn cmp_1_lt_2() {
            let first = Bigint::from_str("1").unwrap();
            let second = Bigint::from_str("2").unwrap();
            assert_eq!(Ordering::Less, first.cmp(&second));
        }

        #[test]
        fn cmp_2_gt_1() {
            let first = Bigint::from_str("2").unwrap();
            let second = Bigint::from_str("1").unwrap();
            assert_eq!(Ordering::Greater, first.cmp(&second));
        }

        #[test]
        fn cmp_3_gt_minus2() {
            let first = Bigint::from_str("3").unwrap();
            let second = Bigint::from_str("-2").unwrap();
            assert_eq!(Ordering::Greater, first.cmp(&second));
        }

        #[test]
        fn cmp_minus3_lt_2() {
            let first = Bigint::from_str("-3").unwrap();
            let second = Bigint::from_str("2").unwrap();
            assert_eq!(Ordering::Less, first.cmp(&second));
        }

        #[test]
        fn cmp_minus1_gt_minus2() {
            let first = Bigint::from_str("-1").unwrap();
            let second = Bigint::from_str("-2").unwrap();
            assert_eq!(Ordering::Greater, first.cmp(&second));
        }

        #[test]
        fn cmp_2_eq_2() {
            let first = Bigint::from_str("2").unwrap();
            let second = Bigint::from_str("2").unwrap();
            assert_eq!(Ordering::Equal, first.cmp(&second));
        }

        #[test]
        fn cmp_1234_gt_123() {
            let first = Bigint::from_str("1234").unwrap();
            let second = Bigint::from_str("123").unwrap();
            assert_eq!(Ordering::Greater, first.cmp(&second));
        }

        #[test]
        fn cmp_123_lt_1234() {
            let first = Bigint::from_str("123").unwrap();
            let second = Bigint::from_str("1234").unwrap();
            assert_eq!(Ordering::Less, first.cmp(&second));
        }

        #[test]
        fn cmp_12239573_lt_37593272() {
            let first = Bigint::from_str("12239573").unwrap();
            let second = Bigint::from_str("37593272").unwrap();
            assert_eq!(Ordering::Less, first.cmp(&second));
        }

        #[test]
        fn cmp_minus123_lt_1234() {
            let first = Bigint::from_str("-123").unwrap();
            let second = Bigint::from_str("1234").unwrap();
            assert_eq!(Ordering::Less, first.cmp(&second));
        }

        #[test]
        fn cmp_minus123_gt_minus1234() {
            let first = Bigint::from_str("-123").unwrap();
            let second = Bigint::from_str("-1234").unwrap();
            assert_eq!(Ordering::Greater, first.cmp(&second));
        }

        #[test]
        fn cmp_zero_eq_zero() {
            let first = Bigint::new();
            let second = Bigint::new();
            assert_eq!(Ordering::Equal, first.cmp(&second));
        }
    }

    mod add {

        use crate::Bigint;
        use std::str::FromStr;

        #[test]
        fn add_1_1_eq_2() {
            let left = Bigint::from_str("1").unwrap();
            let right = Bigint::from_str("1").unwrap();
            let result = left + right;
            assert_eq!(vec![2], result.digits);
        }

        #[test]
        fn add_minus1_minus1_eq_minus2() {
            let left = Bigint::from_str("-1").unwrap();
            let right = Bigint::from_str("-1").unwrap();
            let result = left + right;
            assert_eq!(vec![2], result.digits);
            assert_eq!(-1, result.sign);
        }

        #[test]
        fn add_minus5_minus6_eq_minus11() {
            let left = Bigint::from_str("-5").unwrap();
            let right = Bigint::from_str("-6").unwrap();
            let result = left + right;
            assert_eq!(vec![1, 1], result.digits);
            assert_eq!(-1, result.sign);
        }

        #[test]
        fn add_minus9_minus9_eq_minus18() {
            let left = Bigint::from_str("-9").unwrap();
            let right = Bigint::from_str("-9").unwrap();
            let result = left + right;
            assert_eq!(vec![1, 8], result.digits);
            assert_eq!(-1, result.sign);
        }

        #[test]
        fn add_minus25_50_eq_25() {
            let left = Bigint::from_str("-25").unwrap();
            let right = Bigint::from_str("50").unwrap();
            let result = left + right;
            assert_eq!(vec![2, 5], result.digits);
            assert_eq!(1, result.sign);
        }

        #[test]
        fn add_9_minus9_eq_0() {
            let left = Bigint::from_str("-9").unwrap();
            let right = Bigint::from_str("9").unwrap();
            let result = left + right;
            assert_eq!(std::vec::Vec::<u8>::new(), result.digits);
            assert_eq!(1, result.sign);
            assert!(result.is_zero());
        }

        #[test]
        fn add_1234_4321_eq_5555() {
            let left = Bigint::from_str("1234").unwrap();
            let right = Bigint::from_str("4321").unwrap();
            let result = left + right;
            assert_eq!(vec![5, 5, 5, 5], result.digits);
        }

        #[test]
        fn add_1939_4321_eq_6260() {
            let left = Bigint::from_str("1939").unwrap();
            let right = Bigint::from_str("4321").unwrap();
            let result = left + right;
            assert_eq!(vec![6, 2, 6, 0], result.digits);
        }

        #[test]
        fn add_1939_1_eq_1940() {
            let left = Bigint::from_str("1939").unwrap();
            let right = Bigint::from_str("1").unwrap();
            let result = left + right;
            assert_eq!(vec![1, 9, 4, 0], result.digits);
        }

        #[test]
        fn add_9_9_eq_18() {
            let left = Bigint::from_str("9").unwrap();
            let right = Bigint::from_str("9").unwrap();
            let result = left + right;
            assert_eq!(vec![1, 8], result.digits);
        }

        #[test]
        fn add_0_0_eq_0() {
            let left = Bigint::new();
            let right = Bigint::new();
            let result = left + right;
            assert_eq!(std::vec::Vec::<u8>::new(), result.digits);
        }
    }
}
