"""Availability-aware chronology; event time is NOT known-at time."""
from __future__ import annotations
from dataclasses import dataclass
from datetime import datetime
from .types import ObservationRecord
from ..provenance import instant
from ..errors import AppError

@dataclass(frozen=True)
class ClockReport:
    available_records:tuple[str,...]
    excluded_records:tuple[str,...]
    unresolved_times:tuple[str,...]
    chronology_errors:tuple[str,...]
    def to_dict(self):
        return {k:list(getattr(self,k)) for k in ('available_records','excluded_records','unresolved_times','chronology_errors')}


def available_at(record:ObservationRecord,cutoff:datetime)->bool:
    if not isinstance(record,ObservationRecord) or type(cutoff) is not datetime or cutoff.tzinfo is None:
        raise AppError('DOMAIN_CLOCK','typed observation and aware cutoff required')
    return record.known_at is not None and instant(record.known_at,'known_at')<=cutoff


def validate_clocks(records:list[ObservationRecord],cutoff:datetime|None)->ClockReport:
    if type(records) is not list or len(records)>100000 or any(type(r) is not ObservationRecord for r in records):
        raise AppError('DOMAIN_CLOCK','bounded typed observation batch required')
    if cutoff is not None and (type(cutoff) is not datetime or cutoff.tzinfo is None):
        raise AppError('DOMAIN_CLOCK','cutoff must be timezone aware')
    available=[];excluded=[];unknown=[];errors=[];seen=set()
    for r in records:
        if not r.record_id or r.record_id in seen:raise AppError('DOMAIN_CLOCK','duplicate/empty observation ID')
        seen.add(r.record_id)
        if r.lane not in ('retrospective','hindcast','prospective'):
            raise AppError('DOMAIN_CLOCK','unknown chronology lane')
        if r.event_at is not None:instant(r.event_at,'event_at')
        if r.known_at is None:
            unknown.append(r.record_id);continue
        known=instant(r.known_at,'known_at')
        if r.lane=='prospective':
            if r.frozen_spec_at is None or r.evaluation_start is None:
                errors.append(r.record_id);continue
            freeze=instant(r.frozen_spec_at,'frozen_spec_at')
            start=instant(r.evaluation_start,'evaluation_start')
            if freeze>start:errors.append(r.record_id);continue
        if cutoff is not None and known>cutoff:excluded.append(r.record_id)
        else:available.append(r.record_id)
    return ClockReport(tuple(available),tuple(excluded),tuple(unknown),tuple(errors))
