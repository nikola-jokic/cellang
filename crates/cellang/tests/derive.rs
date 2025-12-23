#![cfg(feature = "derive")]

use cellang::{Env, TypeName};
use cellang::types::{NamedType, Type};
use cellang::value::{IntoValue, TryFromValue, Value};
use cellang::{CelStruct, Runtime};
use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq, CelStruct)]
#[cel(type = "example.Address", doc = "Address record")]
struct Address {
    city: String,
}

#[derive(Clone, Debug, PartialEq, CelStruct)]
#[cel(type = "example.User", doc = "User record")]
struct User {
    #[cel(doc = "Display name")]
    name: String,
    address: Address,
    #[cel(rename = "is_active", doc = "Whether the user is active")]
    active: bool,
    nickname: Option<String>,
    labels: BTreeMap<String, Address>,
}

#[test]
fn cel_struct_generates_metadata_and_conversions() {
    let NamedType::Struct(user_meta) = User::cel_named_type() else {
        panic!("expected struct metadata");
    };
    assert_eq!(user_meta.name.as_str(), User::CEL_TYPE_NAME);
    assert_eq!(user_meta.doc.as_deref(), Some("User record"));

    let address_field = user_meta.fields.get("address").unwrap();
    assert_eq!(address_field.ty, Address::cel_type());

    let active_field = user_meta.fields.get("is_active").unwrap();
    assert_eq!(
        active_field.doc.as_deref(),
        Some("Whether the user is active"),
    );

    let nickname_field = user_meta.fields.get("nickname").unwrap();
    assert_eq!(nickname_field.ty, Type::String);

    let labels_field = user_meta.fields.get("labels").unwrap();
    assert_eq!(
        labels_field.ty,
        Type::map(Type::String, Address::cel_type()),
    );

    let user = User {
        name: "Ada".into(),
        address: Address {
            city: "London".into(),
        },
        active: true,
        nickname: None,
        labels: BTreeMap::from([(
            "home".to_string(),
            Address {
                city: "London".into(),
            },
        )]),
    };
    let value = user.clone().into_value();
    let Value::Struct(strct) = &value else {
        panic!("expected struct value");
    };
    assert!(
        strct
            .fields
            .get("nickname")
            .expect("nickname field missing")
            .is_null()
    );
    match strct.fields.get("labels").expect("labels field missing") {
        Value::Map(map) => assert_eq!(map.len(), 1),
        other => panic!("expected map for labels field, got {}", other.kind()),
    }
    let roundtrip = User::try_from_value(&value).unwrap();
    assert_eq!(roundtrip, user);
}

#[test]
fn register_cel_type_reports_duplicates() {
    let mut builder = Runtime::builder();
    User::register_cel_type(&mut builder).unwrap();
    let err = User::register_cel_type(&mut builder).unwrap_err();
    assert!(
        err.to_string().contains(User::CEL_TYPE_NAME),
        "expected duplicate name in error, got {err}"
    );
}

#[test]
fn register_cel_type_into_env_builder() {
    let mut builder = Env::builder();
    User::register_cel_type(&mut builder).unwrap();
    let env = builder.build();
    let ty = env
        .lookup_type(&TypeName::new(User::CEL_TYPE_NAME))
        .expect("type registered in env");
    assert!(matches!(ty, NamedType::Struct(_)));
}
