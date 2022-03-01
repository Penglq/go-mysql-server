// Copyright 2022 Dolthub, Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package server

import (
	"fmt"
	"sync"

	"github.com/dolthub/vitess/go/mysql"
	"github.com/dolthub/vitess/go/sqltypes"
	"github.com/dolthub/vitess/go/vt/proto/query"

	"github.com/dolthub/go-mysql-server/sql"
)

const (
	defaultResultBufferSize = 1024 * 16
)

type capRequirement uint

const (
	nullCapRequirement      capRequirement = 0
	int8CapRequirement      capRequirement = 4
	uint8CapRequirement     capRequirement = 3
	int16CapRequirement     capRequirement = 6
	uint16CapRequirement    capRequirement = 5
	int24CapRequirement     capRequirement = int32CapRequirement
	uint24CapRequirement    capRequirement = uint32CapRequirement
	int32CapRequirement     capRequirement = 11
	uint32CapRequirement    capRequirement = 10
	int64CapRequirement     capRequirement = 20
	uint64CapRequirement    capRequirement = 20
	float32CapRequirement   capRequirement = 63
	float64CapRequirement   capRequirement = 327
	timestampCapRequirement capRequirement = 26
	dateCapRequirement      capRequirement = 10
	timeCapRequirement      capRequirement = 16
	datetimeCapRequirement  capRequirement = 26
	yearCapRequirement      capRequirement = uint16CapRequirement
)

var resultBuilderPool = sync.Pool{New: newResultByteBuffer}

func newResultByteBuffer() interface{} {
	return make([]byte, defaultResultBufferSize)
}

// resultBuilder builds a sqltypes.Result
type resultBuilder struct {
	sch sql.Schema

	rows [][]sqltypes.Value
	cnt  int

	buf []byte
	pos int
}

type recyclableResult struct {
	res *sqltypes.Result
	buf []byte
}

func (r recyclableResult) recycle() {
	if r.buf != nil {
		resultBuilderPool.Put(r.buf)
	}
}

func newResultBuilder(sch sql.Schema) *resultBuilder {
	rows := valuesSliceFromSchema(sch)

	types := make([]sql.Type, len(sch))
	for i := range types {
		types[i] = sch[i].Type
	}

	buf := resultBuilderPool.New().([]byte)

	return &resultBuilder{
		sch:  sch,
		rows: rows,
		buf:  buf,
	}
}

func (rb *resultBuilder) isFull() bool {
	return rb.cnt >= rowsBatch
}

func (rb *resultBuilder) isEmpty() bool {
	return rb.cnt == 0
}

func (rb *resultBuilder) writeRow(row sql.Row) error {
	err := rb.ensureCapacity(row)
	if err != nil {
		return err
	}

	r := rb.rows[rb.cnt]
	for i, v := range row {
		if v == nil {
			r[i] = sqltypes.NULL
			continue
		}

		dest := rb.buf[:rb.pos]

		r[i], err = rb.sch[i].Type.SQL(dest, v)
		if err != nil {
			return err
		}
		rb.pos += r[i].Len()

		if rb.pos >= len(rb.buf) {
			return fmt.Errorf("failed to ensure capacity")
		}
	}
	rb.cnt++

	return nil
}

func (rb *resultBuilder) build() (r recyclableResult) {
	r = recyclableResult{
		res: &sqltypes.Result{
			Fields:       schemaToFields(rb.sch),
			Rows:         rb.rows[:rb.cnt],
			RowsAffected: uint64(rb.cnt),
		},
		buf: rb.buf,
	}

	// reset builder
	rb.buf = resultBuilderPool.New().([]byte)
	rb.rows = valuesSliceFromSchema(rb.sch)
	rb.pos = 0
	rb.cnt = 0

	return
}

func (rb *resultBuilder) ensureCapacity(row sql.Row) error {
	req, err := capRequirementForRow(rb.sch, row)
	if err != nil {
		return err
	}

	if (rb.pos + int(req)) >= cap(rb.buf) {
		nb := make([]byte, cap(rb.buf)*2)
		copy(nb, rb.buf)
		rb.buf = nb
	}
	return nil
}

func valuesSliceFromSchema(sch sql.Schema) (rows [][]sqltypes.Value) {
	rows = make([][]sqltypes.Value, rowsBatch)
	for i := range rows {
		rows[i] = make([]sqltypes.Value, len(sch))
	}
	return
}

func schemaToFields(s sql.Schema) []*query.Field {
	fields := make([]*query.Field, len(s))
	for i, c := range s {
		var charset uint32 = mysql.CharacterSetUtf8
		if sql.IsBlob(c.Type) {
			charset = mysql.CharacterSetBinary
		}

		fields[i] = &query.Field{
			Name:    c.Name,
			Type:    c.Type.Type(),
			Charset: charset,
		}
	}

	return fields
}

func capRequirementForRow(sch sql.Schema, row sql.Row) (capRequirement, error) {
	var r capRequirement
	for i, col := range sch {
		switch col.Type.Type() {
		case query.Type_NULL_TYPE:
			r += nullCapRequirement
		case query.Type_INT8:
			r += int8CapRequirement
		case query.Type_UINT8:
			r += uint8CapRequirement
		case query.Type_INT16:
			r += int16CapRequirement
		case query.Type_UINT16:
			r += uint16CapRequirement
		case query.Type_INT24:
			r += int24CapRequirement
		case query.Type_UINT24:
			r += uint24CapRequirement
		case query.Type_INT32:
			r += int32CapRequirement
		case query.Type_UINT32:
			r += uint32CapRequirement
		case query.Type_INT64:
			r += int64CapRequirement
		case query.Type_UINT64:
			r += uint64CapRequirement
		case query.Type_FLOAT32:
			r += float32CapRequirement
		case query.Type_FLOAT64:
			r += float64CapRequirement
		case query.Type_TIMESTAMP:
			r += timestampCapRequirement
		case query.Type_DATE:
			r += dateCapRequirement
		case query.Type_TIME:
			r += timeCapRequirement
		case query.Type_DATETIME:
			r += datetimeCapRequirement
		case query.Type_YEAR:
			r += yearCapRequirement

		default:
			switch t := row[i].(type) {
			case string:
				r += capRequirement(len(t))
			case []byte:
				r += capRequirement(len(t))
			default:
				// todo: we can do better for some types
				v, err := col.Type.SQL(nil, t)
				if err != nil {
					return 0, err
				}
				r += capRequirement(v.Len())
			}
		}
	}
	return r, nil
}
