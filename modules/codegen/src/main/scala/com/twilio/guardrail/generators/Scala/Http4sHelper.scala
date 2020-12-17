package com.twilio.guardrail.generators.Scala

import com.twilio.guardrail.languages.ScalaLanguage
import com.twilio.guardrail.protocol.terms.{ ApplicationJson, ContentType, Response, Responses }
import com.twilio.guardrail.StrictProtocolElems

import scala.meta._

object Http4sHelper {
  def generateResponseDefinitions(
      responseClsName: String,
      responses: Responses[ScalaLanguage],
      protocolElems: List[StrictProtocolElems[ScalaLanguage]]
  ): List[Defn] = {
    val isGeneric                         = isDefinitionGeneric(responses)
    val extraTypes: List[Type]            = if (isGeneric) List(t"F") else Nil
    val extraTypeParams: List[Type.Param] = if (isGeneric) List(tparam"F[_]") else Nil

    val responseSuperType     = Type.Name(responseClsName)
    val responseSuperTerm     = Term.Name(responseClsName)
    val responseSuperTemplate = template"${Init(if (isGeneric) Type.Apply(responseSuperType, extraTypes) else responseSuperType, Name(""), List.empty)}"

    val (terms, foldPair) = responses.value
      .map({
        case Response(statusCodeName, valueType, headers) =>
          val responseTerm = Term.Name(s"${statusCodeName.value}")
          val responseName = Type.Name(s"${statusCodeName.value}")

          val foldHandleName = Term.Name(s"handle${statusCodeName.value}")

          val allParams = valueType.map(tpe => (tpe, q"value")).toList ++ headers.value.map(h => (h.tpe, h.term))
          allParams match {
            case Nil if !isGeneric =>
              val foldParameter = param"${foldHandleName}: => A"
              val foldCase      = p"case ${responseSuperTerm}.${responseTerm} => ${foldHandleName}"
              (q"case object $responseTerm extends $responseSuperTemplate", (foldParameter, foldCase))
            case _ =>
              val responseCaseType = if (isGeneric) t"$responseSuperTerm.$responseName[F]" else t"$responseSuperTerm.$responseName"
              val foldParameter    = param"${foldHandleName}: (..${allParams.map(_._1)}) => A"
              val foldCase         = p"case x: $responseCaseType => ${foldHandleName}(..${allParams.map(t => q"x.${t._2}")})"
              (
                q"case class  $responseName[..$extraTypeParams](..${allParams.map(t => param"${t._2}: ${t._1}")}) extends $responseSuperTemplate",
                (foldParameter, foldCase)
              )
          }
      })
      .unzip

    val (foldParams, foldCases) = foldPair.unzip

    // Union
    val recordTypeDefns = responses.value
      .map({
        case response @ Response(_, valueTypeO, headers) =>
          val recordTypeName = s"${response.statusCodeName.value}Record"
          val valueType = valueTypeO.getOrElse(t"Unit")
          val valueField = ("value", valueType)
          val headerFields = headers.value.map(header => (header.term.value, header.tpe))
          val fields = valueField :: headerFields
          makeRecordDefn(recordTypeName, fields)
      })

    val recordConstructors = responses.value
      .map({
        case response @ Response(_, valueTypeO, headers) =>
          val recordType = Type.Name(s"${response.statusCodeName.value}Record")

          val (valueParamName, valueParam) = {
            val valueParamName = q"value"
            val valueType = valueTypeO.getOrElse(t"Unit")
            val valueParam = param"$valueParamName: $valueType"
            (valueParamName, valueParam)
          }

          val (headerParamNames, headerParams) = headers.value.map(header => {
            val headerParamName = header.term
            val headerType = header.tpe
            val headerParam = param"$headerParamName: $headerType"
            (headerParamName, headerParam)
          }).unzip

          val paramNames = valueParamName :: headerParamNames
          val params = valueParam :: headerParams

          val constructorName = Term.Name(s"create${response.statusCodeName.value}Record")
          val constructorBody = paramNames.foldRight[Term](q"HNil")((paramName, tail) => {
            val fieldName = Lit.Symbol(Symbol(paramName.value))
            q"($fieldName ->> $paramName) :: $tail"
          })

          q"def $constructorName(..$params): $recordType = $constructorBody"
      })

    val unionTypeDefn = makeUnionDefn("UnionType", responses.value.map(response => {
      val labelName = response.statusCode.toString
      val recordType = Type.Name(s"${response.statusCodeName.value}Record")
      (labelName, recordType)
    }))

    val foldToUnionCases = responses.value
      .map({
        case response @ Response(_, valueType, headers) =>
          val params = valueType.map(_ => Term.Name("value")).toList ++ headers.value.map(_.term)
          val terms = valueType.fold[Term](q"()")(_ => Term.Name("value")) :: headers.value.map(_.term)
          val labelName = Lit.Int(response.statusCode)
          val constructor = Term.Name(s"create${response.statusCodeName.value}Record")
          if (params.isEmpty && !isGeneric) q"Coproduct[UnionType]($labelName ->> ${Term.Apply(constructor, terms)})"
          else q"(..${params.map(param => param"$param")}) => Coproduct[UnionType]($labelName ->> ${Term.Apply(constructor, terms)})"
      })

    val toUnionDef = q"def toUnion: UnionType = ${Term.Apply(Term.Name("fold"), foldToUnionCases)}"

    val companion = q"""
            object ${Term.Name(responseClsName)} {
              ..$terms

              ..$recordTypeDefns
              ..$recordConstructors
              $unionTypeDefn
            }
          """

    val cls = q"""
        sealed abstract class ${responseSuperType}[..$extraTypeParams] {
          def fold[A](..${foldParams}): A = ${Term.Match(Term.This(Name("")), foldCases)}

          import ${Term.Name(responseClsName)}._
          $toUnionDef
        }
      """
    List[Defn](cls, companion)
  }

  def generateDecoder(tpe: Type, consumes: Seq[ContentType]): Term =
    if (consumes.contains(ApplicationJson) || consumes.isEmpty)
      q"jsonOf[F, $tpe]"
    else
      tpe match {
        case t"Option[$_]" => q"""
                  decodeBy(MediaType.text.plain) { msg =>
                    msg.contentLength.filter(_ > 0).fold[DecodeResult[F, $tpe]](DecodeResult.success(None)){ _ =>
                      DecodeResult.success(decodeString(msg)).flatMap { str =>
                        Json.fromString(str).as[$tpe]
                          .fold(failure =>
                            DecodeResult.failure(InvalidMessageBodyFailure(s"Could not decode response: $$str", Some(failure))),
                            DecodeResult.success(_)
                          )
                      }
                    }
                  }
                """
        case _             => q"EntityDecoder[F, $tpe]"
      }

  def generateEncoder(tpe: Type, produces: Seq[ContentType]): Term =
    if (produces.contains(ApplicationJson) || produces.isEmpty)
      q"jsonEncoderOf[F, $tpe]"
    else
      tpe match {
        case t"Option[$_]" => q"""
                  encodeBy(`Content-Type`(MediaType.text.plain, Charset.`UTF-8`)) { a: $tpe =>
                    a.fold[Entity[F]](Entity.empty)(e => EntityEncoder[F, String].toEntity(e.toString))
                  }
                """
        case _             => q"EntityEncoder[F, $tpe]"
      }

  def generateEntityResponseGenerator(term: Term.Ref): Term =
    q"""
       new org.http4s.dsl.impl.EntityResponseGenerator[F,F] {
          def status = $term
          val liftG = cats.arrow.FunctionK.id
       }
     """

  def isDefinitionGeneric(responses: Responses[ScalaLanguage]): Boolean =
    responses.value.exists { response =>
      response.value.exists {
        case (_, tpe, _) =>
          tpe match {
            case t"fs2.Stream[F,Byte]" => true
            case _                     => false
          }
      }
    }

  private def makeWitnessType(name: String): Type = {
    val nameTerm = Term.Name(name)
    val witnessTerm = q"Witness.$nameTerm"
    Type.Select(witnessTerm, t"T")
  }

  private def makeFieldType(fieldName: String, fieldType: Type): Type = {
    val witness = makeWitnessType(fieldName)
    t"FieldType[$witness, $fieldType]"
  }

  private def makeRecordDefn(recordName: String, fields: List[(String, Type)]): Defn = {
    val recordTypeName = Type.Name(recordName)
    val recordType = fields.foldRight[Type](t"HNil")((field, tail) => {
      val fieldName = s"'${field._1}"
      val head = makeFieldType(fieldName, field._2)
      t"$head :: $tail"
    })
    q"type $recordTypeName = $recordType"
  }

  private def makeUnionDefn(unionName: String, members: List[(String, Type)]): Defn = {
    val unionTypeName = Type.Name(unionName)
    val unionType = members.foldRight[Type](t"CNil")((member, tail) => {
      val head = makeFieldType(member._1, member._2)
      t"$head :+: $tail"
    })
    q"type $unionTypeName = $unionType"
  }
}
