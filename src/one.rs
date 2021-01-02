use std::collections::HashSet;
use std::collections::{HashMap, VecDeque};
use std::ffi::CString;

/// Return true if the given string has all unique characters.
/// This implementation uses a HashSet to track seen characters and is O(n).
///
/// # Examples
///
/// ```
/// assert_eq!(cracking::one::one_unique("abc"), true);
/// assert_eq!(cracking::one::one_unique("aba"), false);
/// ```
pub fn one_unique(s: &str) -> bool {
    let mut set: HashSet<char> = HashSet::new();
    for c in s.chars() {
        if !set.insert(c) {
            return false;
        }
    }
    true
}

/// Return true if the given string has all unique characters.
/// This implementation uses no other data structure and is O(n2).
///
/// # Examples
///
/// ```
/// assert_eq!(cracking::one::one_unique_on2("abc"), true);
/// assert_eq!(cracking::one::one_unique_on2("aba"), false);
/// ```
pub fn one_unique_on2(s: &str) -> bool {
    for (i, c) in s.char_indices() {
        for c2 in s[i + 1..].chars() {
            if c == c2 {
                return false;
            }
        }
    }
    return true;
}

/// Reverse the given CString in place. This function
/// assumes the CString is ASCII, anything else will
/// result in a garbled string and undefined behavior.
///
/// # Examples
///
/// ```
/// use std::ffi::CString;
/// assert_eq!(cracking::one::two_reverse(
///   CString::new("abc").expect("Error")),
///   CString::new("cba").expect("Error")
/// );
/// ```
pub fn two_reverse(s: CString) -> CString {
    let mut bytes = s.into_bytes_with_nul();
    // minus 2 to skip the nul and land on the last char
    let z = bytes.len() - 2;
    for a in 0..bytes.len() {
        let za = z - a;
        if a >= za {
            break;
        }
        let b = bytes[za];
        bytes[z] = bytes[a];
        bytes[a] = b;
    }
    CString::from_vec_with_nul(bytes).expect("CString::from_vec_with_nul failed")
}

/// Return true if the strings are permutations, false otherwise. This function
/// works with any Unicode string HOWEVER it does not look at the grapheme clusters
/// though in most cases it should still be accurate.
///
/// This function is O(n * 2).
///
/// # Examples
///
/// ```
/// assert_eq!(cracking::one::three_permutation("abc", "cba"), true);
/// assert_eq!(cracking::one::three_permutation("aabc", "cba"), false);
/// ```
pub fn three_permutation(s1: &str, s2: &str) -> bool {
    if s1.len() != s2.len() {
        return false;
    }

    // if we limit the scope to just ASCII characters this could be
    // optimized to use a fixed array...
    let mut map: HashMap<char, u16> = HashMap::new();
    s1.chars().for_each(|c| {
        map.insert(c, map.get(&c).map_or(1, |i| i + 1));
    });

    // loop for early return
    for c in s2.chars() {
        match map.get(&c) {
            Some(i) => {
                let i2 = i - 1;
                if i2 == 0 {
                    map.remove(&c);
                } else {
                    map.insert(c, i2);
                }
            }
            None => return false,
        }
    }

    map.is_empty()
}

/// Replace all spaces ' ' with '%20' in place. The passed
/// in string must have enough space to accommodate the extra
/// characters else will be cut off.
///
/// This implementation utilizes an internal queue to guarantee
/// O(n) performance.
///
/// # Examples
///
/// ```
/// use std::ffi::CString;
/// assert_eq!(cracking::one::four_space(
///   CString::new("Mr John Smith    ").expect("Error")),
///   CString::new("Mr%20John%20Smith").expect("Error")
/// );
/// assert_eq!(cracking::one::four_space(
///   CString::new("Mr John Smith").expect("Error")),
///   CString::new("Mr%20John%20S").expect("Error")
/// );
/// assert_eq!(cracking::one::four_space(
///   CString::new("Mr John  Smith").expect("Error")),
///   CString::new("Mr%20John%20%2").expect("Error")
/// );
/// assert_eq!(cracking::one::four_space(
///   CString::new(" ").expect("Error")),
///   CString::new("%").expect("Error")
/// );
/// assert_eq!(cracking::one::four_space(
///   CString::new("   ").expect("Error")),
///   CString::new("%20").expect("Error")
/// );
/// assert_eq!(cracking::one::four_space(
///   CString::new("").expect("Error")),
///   CString::new("").expect("Error")
/// );
/// ```
pub fn four_space(s: CString) -> CString {
    let mut bytes = s.into_bytes_with_nul();
    if bytes.len() == 0 {
        return CString::from_vec_with_nul(bytes).expect("CString::from_vec failed");
    }

    let mut que: VecDeque<u8> = VecDeque::new();

    for i in 0..bytes.len() - 1 {
        let cur = bytes[i];
        if b' ' == cur {
            que.push_back(b'%');
            que.push_back(b'2');
            que.push_back(b'0');
        }

        if !que.is_empty() {
            if b' ' != cur {
                que.push_back(cur);
            }
            bytes[i] = que.pop_front().expect("VecDeque::pop_front failed");
        }
    }

    CString::from_vec_with_nul(bytes).expect("CString::from_vec failed")
}

/// Book solution: Replace all spaces ' ' with '%20' in place.
/// It is assumed the passed in string has enough space to
/// accommodate the extra characters.
///
/// This implemenation is O(n*2)
///
/// # Examples
///
/// ```
/// use std::ffi::CString;
/// assert_eq!(cracking::one::four_space(
///   CString::new("Mr John Smith    ").expect("Error")),
///   CString::new("Mr%20John%20Smith").expect("Error")
/// );
/// ```
pub fn four_space_solution(s: CString, length: usize) -> CString {
    let mut bytes = s.into_bytes_with_nul();
    if bytes.len() == 0 {
        return CString::from_vec_with_nul(bytes).expect("CString::from_vec failed");
    }

    let mut space_count: usize = 0;

    for i in 0..length {
        if b' ' == bytes[i] {
            space_count += 1;
        }
    }

    let mut new_length: usize = (length + space_count * 2) as usize;
    bytes[new_length] = b'\0';
    for i in length - 1..0 {
        if bytes[i] == b' ' {
            bytes[new_length - 1] = b'0';
            bytes[new_length - 2] = b'2';
            bytes[new_length - 3] = b'%';
            new_length = new_length - 3;
        } else {
            bytes[new_length] = bytes[i];
            new_length = new_length - 1;
        }
    }

    CString::from_vec_with_nul(bytes).expect("CString::from_vec failed")
}

/// Simple compression of the given string with O(n) performance.
///
/// # Examples
///
/// ```
/// assert_eq!(cracking::one::five_compress("aabcccccaaa"), "a2b1c5a3");
/// ```
pub fn five_compress(s: &str) -> String {
    let mut str = String::with_capacity(s.len());
    let mut count: u32 = 1;
    let mut cur: char = '\0';

    for c in s.chars() {
        if str.is_empty() {
            str.push(c);
            cur = c;
        } else if cur != c {
            str.push_str(count.to_string().as_str());
            str.push(c);
            cur = c;
            count = 1;
        } else {
            count += 1;
        }
    }

    str.push_str(count.to_string().as_str());

    if str.len() > s.len() {
        String::from(s)
    } else {
        str
    }
}

/// Rotate a NxN matrix 90 degrees in place. Anything other than a NxN matrix (ie. MxN) will
/// result in a panic. Performance is O(n*n).
///
/// # Examples
///
/// ```
/// #[rustfmt::skip]
/// assert_eq!(
///     cracking::one::six_image_turn(&mut [
///         &mut [10, 11, 12, 13, 14, 15, 16, 17],
///         &mut [20, 21, 22, 23, 24, 25, 26, 27],
///         &mut [30, 31, 32, 33, 34, 35, 36, 37],
///         &mut [40, 41, 42, 43, 44, 45, 46, 47],
///         &mut [50, 51, 52, 53, 54, 55, 56, 57],
///         &mut [60, 61, 62, 63, 64, 65, 66, 67],
///         &mut [70, 71, 72, 73, 74, 75, 76, 77],
///         &mut [80, 81, 82, 83, 84, 85, 86, 87]]),
///         [
///              [80, 70, 60, 50, 40, 30, 20, 10],
///              [81, 71, 61, 51, 41, 31, 21, 11],
///              [82, 72, 62, 52, 42, 32, 22, 12],
///              [83, 73, 63, 53, 43, 33, 23, 13],
///              [84, 74, 64, 54, 44, 34, 24, 14],
///              [85, 75, 65, 55, 45, 35, 25, 15],
///              [86, 76, 66, 56, 46, 36, 26, 16],
///              [87, 77, 67, 57, 47, 37, 27, 17]]
/// );
/// ```
pub fn six_image_turn<'a>(matrix: &'a mut [&'a mut [u32]]) -> &'a mut [&'a mut [u32]] {
    // figure out the number of boxes to process is N / 2, discard the remainder:
    // a 7x7 box will have 3 boxes to process around (7 / 2 = 3)

    // when moving on to the next box, increment x and y by one.

    // the number of times we will need to iterate around the current
    // box is the current box length - 1

    // for each point, we move its 90 degree position by:
    // xx = x, x = (N - 1) - y, y = xx

    let len = matrix.len();
    let mut cur_box_size = len;
    let boxes = len / 2;

    // println!("number of boxes to process: {}", boxes);

    for b in 0..boxes {
        let start_x = b;
        let start_y = b;

        // println!("processing box {} of {}x{}", b, cur_box_size, cur_box_size);

        for x in start_x..(start_x + cur_box_size - 1) {
            // println!("starting iteration at {} / {} ", x, start_y);

            let mut cur_x = x;
            let mut cur_y = start_y;
            let mut cur_val = matrix[cur_y][cur_x];

            loop {
                let next_x = len - 1 - cur_y;
                let next_y = cur_x;
                let next_val = matrix[next_y][next_x];
                matrix[next_y][next_x] = cur_val;

                if next_x == x && next_y == start_y {
                    break;
                } else {
                    cur_x = next_x;
                    cur_y = next_y;
                    cur_val = next_val;
                }
            }
        }

        cur_box_size -= 2;
    }

    matrix
}

/// If an element in the MxN matrix is 0, then set the entire
/// row and column to 0. Performance is O(m*n).
///
/// # Examples
///
/// ```
/// #[rustfmt::skip]
/// let m1: &mut [&mut [u32]] = &mut [
/// &mut [10, 11,  0,  0     ],
/// &mut [20,  0, 22         ],
/// &mut [30, 31, 32, 33, 34 ]];
/// let r1 = cracking::one::seven_zero(m1);
///
/// #[rustfmt::skip]
/// assert_eq!(r1[0], [0,  0, 0, 0    ]);
/// #[rustfmt::skip]
/// assert_eq!(r1[1], [0,  0, 0       ]);
/// assert_eq!(r1[2], [30, 0, 0, 0, 34]);
/// ```
pub fn seven_zero<'a>(matrix: &'a mut [&'a mut [u32]]) -> &'a mut [&'a mut [u32]] {
    let mut set: HashSet<usize> = HashSet::new();
    let rows = matrix.len();

    for row in 0..rows {
        let cols = matrix[row].len();
        let mut zero_row = false;

        for col in 0..cols {
            if matrix[row][col] == 0 {
                zero_row = true;
                set.insert(col);
            }
            // else if set.contains(&col) {
            //     matrix[row][col] = 0;
            // }
        }

        if zero_row {
            for col in 0..cols {
                matrix[row][col] = 0;
            }
        }
    }

    // ensure the cols we encountered are zero'd
    for col in set {
       for row in 0..rows {
           if matrix[row].len() > col {
               matrix[row][col] = 0
           }
       }
    }

    matrix
}

/// Return true if s2 is a rotation of s1.
///
/// # Examples
///
/// ```
/// assert_eq!(cracking::one::eight_rotation("waterbottle", "erbottlewat"), true);
/// assert_eq!(cracking::one::eight_rotation("waterbottle", "waterbottle"), true);
/// ```
pub fn eight_rotation(s1: &str, s2: &str) -> bool {
    if s1.len() > 0 && s1.len() == s2.len() {
        let mut s1s1 = String::from(s1);
        s1s1.push_str(s1);
        s1s1.contains(s2)
    } else {
        false
    }
}

#[cfg(test)]
mod tests {
    use std::ffi::CString;

    use crate::one::five_compress;
    use crate::one::four_space;
    use crate::one::one_unique;
    use crate::one::one_unique_on2;
    use crate::one::six_image_turn;
    use crate::one::three_permutation;
    use crate::one::two_reverse;
    use crate::one::seven_zero;
    use crate::one::eight_rotation;

    #[test]
    fn test_one_one_unique() {
        assert_eq!(one_unique("abc"), true);
        assert_eq!(one_unique("aba"), false);
        assert_eq!(one_unique(""), true);
        assert_eq!(one_unique("a"), true);
        assert_eq!(one_unique("ab"), true);
        assert_eq!(one_unique("aa"), false);
    }

    #[test]
    fn test_one_one_unique_on2() {
        assert_eq!(one_unique_on2("abc"), true);
        assert_eq!(one_unique_on2("aba"), false);
        assert_eq!(one_unique_on2(""), true);
        assert_eq!(one_unique_on2("a"), true);
        assert_eq!(one_unique_on2("ab"), true);
        assert_eq!(one_unique_on2("aa"), false);
    }

    #[test]
    fn test_one_two_reverse() {
        let abc = CString::new("abc").expect("Error");
        let abc_ptr = abc.as_ptr();

        let cba = two_reverse(abc);
        let cba_ptr = cba.as_ptr();

        assert_eq!(cba, CString::new("cba").expect("Error"));
        assert_eq!(abc_ptr, cba_ptr);
    }

    #[test]
    fn test_one_three_permutation() {
        assert_eq!(three_permutation("abc", "cab"), true);
        assert_eq!(three_permutation("aabc", "cab"), false);
        assert_eq!(three_permutation("aabc", "acab"), true);
        assert_eq!(three_permutation("", ""), true);
        assert_eq!(three_permutation("a", ""), false);
        assert_eq!(three_permutation("aaaaaaaa", "aaaaaa"), false);
        assert_eq!(three_permutation("aaaaaaaa", "aaaaaaaa"), true);
    }

    #[test]
    fn test_one_four_space() {
        let j = CString::new("Mr John Smith    ").expect("Error");
        let j_ptr = j.as_ptr();

        let js = four_space(j);
        let js_ptr = js.as_ptr();

        assert_eq!(js, CString::new("Mr%20John%20Smith").expect("Error"));
        assert_eq!(j_ptr, js_ptr);
        assert_eq!(
            four_space(CString::new("Mr John Smith").expect("Error")),
            CString::new("Mr%20John%20S").expect("Error")
        );
        assert_eq!(
            four_space(CString::new("Mr John  Smith").expect("Error")),
            CString::new("Mr%20John%20%2").expect("Error")
        );
        assert_eq!(
            four_space(CString::new("").expect("Error")),
            CString::new("").expect("Error")
        );
        assert_eq!(
            four_space(CString::new(" ").expect("Error")),
            CString::new("%").expect("Error")
        );
        assert_eq!(
            four_space(CString::new("   ").expect("Error")),
            CString::new("%20").expect("Error")
        );
    }

    #[test]
    fn test_one_four_space_solution() {
        let j = CString::new("Mr John Smith    ").expect("Error");
        let j_ptr = j.as_ptr();

        let js = four_space(j);
        let js_ptr = js.as_ptr();

        assert_eq!(js, CString::new("Mr%20John%20Smith").expect("Error"));
        assert_eq!(j_ptr, js_ptr);
    }

    #[test]
    fn test_one_five_compress() {
        assert_eq!(five_compress("aabcccccaaa"), "a2b1c5a3");
    }

    #[test]
    fn test_one_six_image_turn() {
        #[rustfmt::skip]
        assert_eq!(
            six_image_turn(&mut [
                &mut [10, 11, 12],
                &mut [20, 21, 22],
                &mut [30, 31, 32]]),
                [
                     [30, 20, 10],
                     [31, 21, 11],
                     [32, 22, 12]]
        );

        #[rustfmt::skip]
        assert_eq!(
            six_image_turn(&mut [
                &mut [10, 11, 12, 13],
                &mut [20, 21, 22, 23],
                &mut [30, 31, 32, 33],
                &mut [40, 41, 42, 43]]),
                [
                     [40, 30, 20, 10],
                     [41, 31, 21, 11],
                     [42, 32, 22, 12],
                     [43, 33, 23, 13]]
        );

        #[rustfmt::skip]
        assert_eq!(
            six_image_turn(&mut [
                &mut [10, 11, 12, 13, 14],
                &mut [20, 21, 22, 23, 24],
                &mut [30, 31, 32, 33, 34],
                &mut [40, 41, 42, 43, 44],
                &mut [50, 51, 52, 53, 54]]),
                [
                     [50, 40, 30, 20, 10],
                     [51, 41, 31, 21, 11],
                     [52, 42, 32, 22, 12],
                     [53, 43, 33, 23, 13],
                     [54, 44, 34, 24, 14]]
                );

        #[rustfmt::skip]
        assert_eq!(
            six_image_turn(&mut [
                &mut [10, 11, 12, 13, 14, 15],
                &mut [20, 21, 22, 23, 24, 25],
                &mut [30, 31, 32, 33, 34, 35],
                &mut [40, 41, 42, 43, 44, 45],
                &mut [50, 51, 52, 53, 54, 55],
                &mut [60, 61, 62, 63, 64, 65]]),
                [
                     [60, 50, 40, 30, 20, 10],
                     [61, 51, 41, 31, 21, 11],
                     [62, 52, 42, 32, 22, 12],
                     [63, 53, 43, 33, 23, 13],
                     [64, 54, 44, 34, 24, 14],
                     [65, 55, 45, 35, 25, 15]]
        );

        #[rustfmt::skip]
        assert_eq!(
            six_image_turn(&mut [
                &mut [10, 11, 12, 13, 14, 15, 16],
                &mut [20, 21, 22, 23, 24, 25, 26],
                &mut [30, 31, 32, 33, 34, 35, 36],
                &mut [40, 41, 42, 43, 44, 45, 46],
                &mut [50, 51, 52, 53, 54, 55, 56],
                &mut [60, 61, 62, 63, 64, 65, 66],
                &mut [70, 71, 72, 73, 74, 75, 76]]),
                [
                     [70, 60, 50, 40, 30, 20, 10],
                     [71, 61, 51, 41, 31, 21, 11],
                     [72, 62, 52, 42, 32, 22, 12],
                     [73, 63, 53, 43, 33, 23, 13],
                     [74, 64, 54, 44, 34, 24, 14],
                     [75, 65, 55, 45, 35, 25, 15],
                     [76, 66, 56, 46, 36, 26, 16]]
        );

        #[rustfmt::skip]
        assert_eq!(
            six_image_turn(&mut [
                &mut [10, 11, 12, 13, 14, 15, 16, 17],
                &mut [20, 21, 22, 23, 24, 25, 26, 27],
                &mut [30, 31, 32, 33, 34, 35, 36, 37],
                &mut [40, 41, 42, 43, 44, 45, 46, 47],
                &mut [50, 51, 52, 53, 54, 55, 56, 57],
                &mut [60, 61, 62, 63, 64, 65, 66, 67],
                &mut [70, 71, 72, 73, 74, 75, 76, 77],
                &mut [80, 81, 82, 83, 84, 85, 86, 87]]),
                [
                     [80, 70, 60, 50, 40, 30, 20, 10],
                     [81, 71, 61, 51, 41, 31, 21, 11],
                     [82, 72, 62, 52, 42, 32, 22, 12],
                     [83, 73, 63, 53, 43, 33, 23, 13],
                     [84, 74, 64, 54, 44, 34, 24, 14],
                     [85, 75, 65, 55, 45, 35, 25, 15],
                     [86, 76, 66, 56, 46, 36, 26, 16],
                     [87, 77, 67, 57, 47, 37, 27, 17]]
        );
    }

    #[test]
    fn test_one_seven_zero() {
        #[rustfmt::skip]
        let m1: &mut [&mut [u32]] = &mut [
            &mut [10, 0     ],
            &mut [20, 21, 22],
            &mut [30, 31, 32]];
        let r1 = seven_zero(m1);

        // compare each row individually to get around
        // a compiler error because of the MxN matrix
        // the assert_eq macro expects all the rows to
        // be the same length...
        #[rustfmt::skip]
        assert_eq!(r1[0], [0,  0    ]);
        assert_eq!(r1[1], [20, 0, 22]);
        assert_eq!(r1[2], [30, 0, 32]);

        #[rustfmt::skip]
        let m1: &mut [&mut [u32]] = &mut [
            &mut [10, 11,  0],
            &mut [20, 21, 22],
            &mut [30, 31,   ]];
        let r1 = seven_zero(m1);

        assert_eq!(r1[0], [0,  0,  0]);
        assert_eq!(r1[1], [20, 21, 0]);
        #[rustfmt::skip]
        assert_eq!(r1[2], [30, 31   ]);

        #[rustfmt::skip]
        let m1: &mut [&mut [u32]] = &mut [
            &mut [10, 11,  0],
            &mut [20,  0, 22],
            &mut [30, 31,   ]];
        let r1 = seven_zero(m1);

        assert_eq!(r1[0], [0,  0, 0]);
        assert_eq!(r1[1], [0,  0, 0]);
        #[rustfmt::skip]
        assert_eq!(r1[2], [30, 0   ]);

        #[rustfmt::skip]
        let m1: &mut [&mut [u32]] = &mut [
            &mut [10, 11,  0,  0     ],
            &mut [20, 21, 22         ],
            &mut [0,  31, 32, 33, 34 ]];
        let r1 = seven_zero(m1);

        #[rustfmt::skip]
        assert_eq!(r1[0], [0,  0, 0, 0    ]);
        #[rustfmt::skip]
        assert_eq!(r1[1], [0, 21, 0       ]);
        assert_eq!(r1[2], [0,  0, 0, 0, 0 ]);

        #[rustfmt::skip]
        let m1: &mut [&mut [u32]] = &mut [
            &mut [10, 11,  0,  0     ],
            &mut [20,  0, 22         ],
            &mut [30, 31, 32, 33, 34 ]];
        let r1 = seven_zero(m1);

        #[rustfmt::skip]
        assert_eq!(r1[0], [0,  0, 0, 0    ]);
        #[rustfmt::skip]
        assert_eq!(r1[1], [0,  0, 0       ]);
        assert_eq!(r1[2], [30, 0, 0, 0, 34]);
    }

    #[test]
    fn test_one_eight_rotation() {
        assert_eq!(eight_rotation("waterbottle", "erbottlewat"), true);
        assert_eq!(eight_rotation("waterbottle", "waterbottle"), true);
        assert_eq!(eight_rotation("waterbottle", "bottle"), false);
        assert_eq!(eight_rotation("waterbottle", "watebottlee"), false);
    }

}
