use std::borrow::Cow;

pub struct FizzBuzzer {
    labels: [String; 3],
}

impl FizzBuzzer {
    pub fn new(labels: [String; 3]) -> Self {
        FizzBuzzer { labels }
    }

    /// Връщаме нова структура `FizzBuzzerIter`, която има връзка с оригиналния FizzBuzzer и
    /// каквото още ѝ трябва, за да може да връща резултати.
    pub fn iter(&self) -> FizzBuzzerIter {
        FizzBuzzerIter {
            fizzbuzzer: self,
            state: 0,
        }
    }
}

pub struct FizzBuzzerIter<'a> {
    fizzbuzzer: &'a FizzBuzzer,
    state: i32, // каквито други полета ви трябват
}

impl<'a> Iterator for FizzBuzzerIter<'a> {
    type Item = Cow<'a, str>;

    /// Очакваме всяко извикване на тази функция да връща следващото естествено число, започващо от
    /// 1:
    ///
    /// - Ако числото се дели на 3, връщаме `Cow::Borrowed`, държащо reference към `labels[0]`
    /// - Ако числото се дели на 5, връщаме `Cow::Borrowed`, държащо reference към `labels[1]`
    /// - Ако числото се дели на 15, връщаме `Cow::Borrowed`, държащо reference към `labels[2]`
    /// - Иначе, връщаме `Cow::Owned`, държащо числото, конвертирано до `String`
    ///
    fn next(&mut self) -> Option<Self::Item> {
        self.state += 1;
        match self.state {
            state if state % 15 == 0 => Some(Cow::Borrowed(&self.fizzbuzzer.labels[2])),
            state if state % 5 == 0 => Some(Cow::Borrowed(&self.fizzbuzzer.labels[1])),
            state if state % 3 == 0 => Some(Cow::Borrowed(&self.fizzbuzzer.labels[0])),
            _ => Some(Cow::Owned(self.state.to_string())),
        }
    }
}
