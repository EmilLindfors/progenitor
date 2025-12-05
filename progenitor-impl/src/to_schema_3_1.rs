// Copyright 2025 Oxide Computer Company

//! Schema conversion for OpenAPI 3.1 specs.
//!
//! This module converts `openapiv3_1::Schema` to `schemars::schema::Schema`.
//! OpenAPI 3.1 uses JSON Schema draft 2020-12 which has different semantics
//! from OpenAPI 3.0's modified JSON Schema subset.

use indexmap::IndexMap;
use schemars::schema::SingleOrVec;

use crate::to_schema::ToSchema;

impl ToSchema for openapiv3_1::Schema {
    fn to_schema(&self) -> schemars::schema::Schema {
        match self {
            openapiv3_1::Schema::Bool(b) => schemars::schema::Schema::Bool(*b),
            openapiv3_1::Schema::Object(obj) => convert_object(obj).into(),
            // Handle future variants - fallback to permissive schema
            _ => schemars::schema::Schema::Bool(true),
        }
    }
}

impl ToSchema for openapiv3_1::RefOr<openapiv3_1::Schema> {
    fn to_schema(&self) -> schemars::schema::Schema {
        match self {
            openapiv3_1::RefOr::Ref(r) => {
                schemars::schema::SchemaObject::new_ref(r.ref_location.clone()).into()
            }
            openapiv3_1::RefOr::T(schema) => schema.to_schema(),
        }
    }
}

fn convert_object(obj: &openapiv3_1::schema::Object) -> schemars::schema::SchemaObject {
    let metadata = schemars::schema::Metadata {
        id: if obj.id.is_empty() {
            None
        } else {
            Some(obj.id.clone())
        },
        title: if obj.title.is_empty() {
            None
        } else {
            Some(obj.title.clone())
        },
        description: if obj.description.is_empty() {
            None
        } else {
            Some(obj.description.clone())
        },
        default: obj.default.clone(),
        deprecated: obj.deprecated.unwrap_or(false),
        read_only: obj.read_only.unwrap_or(false),
        write_only: obj.write_only.unwrap_or(false),
        examples: obj.examples.clone(),
    };

    let metadata = Some(Box::new(metadata)).reduce();

    // Handle $ref - if present, create a reference schema
    if !obj.reference.is_empty() {
        return schemars::schema::SchemaObject {
            metadata,
            reference: Some(obj.reference.clone()),
            ..Default::default()
        };
    }

    // Convert instance type from openapiv3_1::Types to schemars
    let instance_type = obj.schema_type.as_ref().map(convert_types);

    // Convert string validation
    let string = if obj.pattern.is_some()
        || obj.min_length.is_some()
        || obj.max_length.is_some()
    {
        Some(Box::new(schemars::schema::StringValidation {
            max_length: obj.max_length.map(|v| v as u32),
            min_length: obj.min_length.map(|v| v as u32),
            pattern: obj.pattern.clone(),
        }))
    } else {
        None
    };

    // Convert number validation
    // OpenAPI 3.1 uses numeric exclusive values (not booleans like 3.0)
    let number = if obj.multiple_of.is_some()
        || obj.minimum.is_some()
        || obj.maximum.is_some()
        || obj.exclusive_minimum.is_some()
        || obj.exclusive_maximum.is_some()
    {
        Some(Box::new(schemars::schema::NumberValidation {
            multiple_of: obj.multiple_of.map(|v| v.into_inner()),
            maximum: obj.maximum.map(|v| v.into_inner()),
            exclusive_maximum: obj.exclusive_maximum.map(|v| v.into_inner()),
            minimum: obj.minimum.map(|v| v.into_inner()),
            exclusive_minimum: obj.exclusive_minimum.map(|v| v.into_inner()),
        }))
    } else {
        None
    };

    // Convert object validation
    let object = if !obj.properties.is_empty()
        || !obj.required.is_empty()
        || obj.additional_properties.is_some()
        || obj.min_properties.is_some()
        || obj.max_properties.is_some()
    {
        Some(Box::new(schemars::schema::ObjectValidation {
            max_properties: obj.max_properties.map(|v| v as u32),
            min_properties: obj.min_properties.map(|v| v as u32),
            required: obj.required.iter().cloned().collect(),
            properties: convert_properties(&obj.properties),
            pattern_properties: convert_properties(&obj.pattern_properties),
            additional_properties: obj
                .additional_properties
                .as_ref()
                .map(|s| Box::new(s.to_schema())),
            property_names: obj
                .property_names
                .as_ref()
                .map(|s| Box::new(s.to_schema())),
        }))
    } else {
        None
    };

    // Convert array validation
    let array = if obj.items.is_some()
        || obj.min_items.is_some()
        || obj.max_items.is_some()
        || obj.unique_items.is_some()
        || obj.contains.is_some()
    {
        Some(Box::new(schemars::schema::ArrayValidation {
            items: obj
                .items
                .as_ref()
                .map(|s| SingleOrVec::Single(Box::new(s.to_schema()))),
            additional_items: obj
                .additional_items
                .as_ref()
                .map(|s| Box::new(s.to_schema())),
            max_items: obj.max_items.map(|v| v as u32),
            min_items: obj.min_items.map(|v| v as u32),
            unique_items: obj.unique_items,
            contains: obj.contains.as_ref().map(|s| Box::new(s.to_schema())),
        }))
    } else {
        None
    };

    // Convert subschemas (oneOf, anyOf, allOf, not)
    let subschemas = if obj.one_of.is_some()
        || obj.any_of.is_some()
        || !obj.all_of.is_empty()
        || obj.not.is_some()
    {
        Some(Box::new(schemars::schema::SubschemaValidation {
            all_of: if obj.all_of.is_empty() {
                None
            } else {
                Some(obj.all_of.iter().map(ToSchema::to_schema).collect())
            },
            any_of: obj
                .any_of
                .as_ref()
                .map(|v| v.iter().map(ToSchema::to_schema).collect()),
            one_of: obj
                .one_of
                .as_ref()
                .map(|v| v.iter().map(ToSchema::to_schema).collect()),
            not: obj.not.as_ref().map(|s| Box::new(s.to_schema())),
            if_schema: obj.if_cond.as_ref().map(|s| Box::new(s.to_schema())),
            then_schema: obj.then.as_ref().map(|s| Box::new(s.to_schema())),
            else_schema: obj.else_cond.as_ref().map(|s| Box::new(s.to_schema())),
        }))
    } else {
        None
    };

    // Convert enum values
    let enum_values = obj.enum_values.clone();

    // Convert const value
    let const_value = obj.const_value.clone();

    // Convert format
    let format = if obj.format.is_empty() {
        None
    } else {
        Some(obj.format.clone())
    };

    // Convert extensions
    let extensions: schemars::Map<String, serde_json::Value> = obj
        .extensions
        .as_ref()
        .map(|ext| ext.iter().map(|(k, v)| (k.clone(), v.clone())).collect())
        .unwrap_or_default();

    schemars::schema::SchemaObject {
        metadata,
        instance_type,
        format,
        enum_values,
        const_value,
        subschemas,
        number,
        string,
        array,
        object,
        reference: None,
        extensions,
    }
}

/// Convert openapiv3_1 Types to schemars instance type
fn convert_types(types: &openapiv3_1::schema::Types) -> SingleOrVec<schemars::schema::InstanceType> {
    match types {
        openapiv3_1::schema::Types::Single(t) => SingleOrVec::Single(Box::new(convert_type(*t))),
        openapiv3_1::schema::Types::Multi(ts) => {
            SingleOrVec::Vec(ts.iter().map(|t| convert_type(*t)).collect())
        }
    }
}

/// Convert a single openapiv3_1 Type to schemars InstanceType
fn convert_type(t: openapiv3_1::schema::Type) -> schemars::schema::InstanceType {
    match t {
        openapiv3_1::schema::Type::Array => schemars::schema::InstanceType::Array,
        openapiv3_1::schema::Type::Boolean => schemars::schema::InstanceType::Boolean,
        openapiv3_1::schema::Type::Integer => schemars::schema::InstanceType::Integer,
        openapiv3_1::schema::Type::Null => schemars::schema::InstanceType::Null,
        openapiv3_1::schema::Type::Number => schemars::schema::InstanceType::Number,
        openapiv3_1::schema::Type::Object => schemars::schema::InstanceType::Object,
        openapiv3_1::schema::Type::String => schemars::schema::InstanceType::String,
        // Handle future variants - default to object
        _ => schemars::schema::InstanceType::Object,
    }
}

/// Convert properties map
fn convert_properties(
    properties: &IndexMap<String, openapiv3_1::Schema>,
) -> schemars::Map<String, schemars::schema::Schema> {
    properties
        .iter()
        .map(|(k, v)| (k.clone(), v.to_schema()))
        .collect()
}

trait OptionReduce {
    fn reduce(self) -> Self;
}

// If an Option is `Some` of its default value, we can simplify that to `None`
impl<T> OptionReduce for Option<T>
where
    T: Default + PartialEq + std::fmt::Debug,
{
    fn reduce(self) -> Self {
        match &self {
            Some(s) if s != &T::default() => self,
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    #[test]
    fn test_simple_string_schema() {
        let schema_json = json!({
            "type": "string"
        });
        let oa_schema: openapiv3_1::Schema = serde_json::from_value(schema_json).unwrap();
        let converted = oa_schema.to_schema();

        let obj = converted.into_object();
        assert_eq!(
            obj.instance_type,
            Some(SingleOrVec::Single(Box::new(
                schemars::schema::InstanceType::String
            )))
        );
    }

    #[test]
    fn test_nullable_string_via_type_array() {
        // OpenAPI 3.1 style nullable using type array
        let schema_json = json!({
            "type": ["string", "null"]
        });
        let oa_schema: openapiv3_1::Schema = serde_json::from_value(schema_json).unwrap();
        let converted = oa_schema.to_schema();

        let obj = converted.into_object();
        match obj.instance_type {
            Some(SingleOrVec::Vec(types)) => {
                assert_eq!(types.len(), 2);
                assert!(types.contains(&schemars::schema::InstanceType::String));
                assert!(types.contains(&schemars::schema::InstanceType::Null));
            }
            _ => panic!("Expected type array"),
        }
    }

    #[test]
    fn test_exclusive_minimum_as_number() {
        // OpenAPI 3.1 uses numeric exclusiveMinimum (not boolean like 3.0)
        let schema_json = json!({
            "type": "integer",
            "exclusiveMinimum": 0
        });
        let oa_schema: openapiv3_1::Schema = serde_json::from_value(schema_json).unwrap();
        let converted = oa_schema.to_schema();

        let obj = converted.into_object();
        assert_eq!(obj.number.unwrap().exclusive_minimum, Some(0.0));
    }

    #[test]
    fn test_ref_schema() {
        let schema_json = json!({
            "$ref": "#/components/schemas/Pet"
        });
        let oa_schema: openapiv3_1::Schema = serde_json::from_value(schema_json).unwrap();
        let converted = oa_schema.to_schema();

        let obj = converted.into_object();
        assert_eq!(obj.reference, Some("#/components/schemas/Pet".to_string()));
    }

    #[test]
    fn test_one_of() {
        let schema_json = json!({
            "oneOf": [
                { "type": "string" },
                { "type": "integer" }
            ]
        });
        let oa_schema: openapiv3_1::Schema = serde_json::from_value(schema_json).unwrap();
        let converted = oa_schema.to_schema();

        let obj = converted.into_object();
        assert!(obj.subschemas.is_some());
        let subschemas = obj.subschemas.unwrap();
        assert!(subschemas.one_of.is_some());
        assert_eq!(subschemas.one_of.unwrap().len(), 2);
    }
}
