use super::*;
use core::fmt;
use core::marker::PhantomData;
use ext_serde::{
    de::{Deserialize, Deserializer, SeqAccess, Visitor},
    ser::{Serialize, SerializeSeq, Serializer},
};

impl<A, T> serde::Serialize for RangeSet<A>
where
    A: smallvec::Array<Item = std::ops::RangeInclusive<T>> + Eq + std::fmt::Debug,
    T: PrimInt + std::fmt::Debug + serde::Serialize,
{
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut state = serializer.serialize_seq(Some(self.ranges.len()))?;
        for item in self.ranges.iter() {
            state.serialize_element(&item)?;
        }
        state.end()
    }
}

impl<'de, A, T> Deserialize<'de> for RangeSet<A>
where
    A: smallvec::Array<Item = std::ops::RangeInclusive<T>> + Eq + std::fmt::Debug,
    T: PrimInt + std::fmt::Debug + Deserialize<'de>,
{
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_seq(RangeSetVisitor {
            phantom: PhantomData,
        })
    }
}

struct RangeSetVisitor<A> {
    phantom: PhantomData<A>,
}

impl<'de, A, T> Visitor<'de> for RangeSetVisitor<A>
where
    A: smallvec::Array<Item = std::ops::RangeInclusive<T>> + Eq + std::fmt::Debug,
    T: PrimInt + std::fmt::Debug + Deserialize<'de>,
{
    type Value = RangeSet<A>;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("a sequence")
    }

    fn visit_seq<B>(self, mut seq: B) -> Result<Self::Value, B::Error>
    where
        B: SeqAccess<'de>,
    {
        let len = seq.size_hint().unwrap_or(0);
        let mut values = RangeSet::with_capacity(len);

        while let Some(value) = seq.next_element()? {
            values.insert_range(value);
        }

        Ok(values)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ops::RangeInclusive;

    #[test]
    fn round_trip() {
        let mut original: RangeSet<[RangeInclusive<u32>; 2]> = RangeSet::new();
        original.insert_range(1..=10);
        original.insert_range(100..=100);

        let serialized = serde_json::to_vec(&original).unwrap();
        let deserialized = serde_json::from_slice(&serialized).unwrap();

        assert_eq!(original, deserialized);
    }
}
