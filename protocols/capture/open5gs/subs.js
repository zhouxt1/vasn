// subscribers IMSI 999700000000001.. NUE (NUE set by --eval before this file)
for (let i = 1; i <= NUE; i++) {
  const imsi = '99970' + String(i).padStart(10, '0');
  db.subscribers.updateOne({imsi: imsi}, {$set: {
    imsi: imsi, msisdn: [], imeisv: '4370816125816151', mme_host: [], mme_realm: [], purge_flag: [],
    security: {k: '465B5CE8B199B49FAA5F0A2EE238A6BC', op: null, opc: 'E8ED289DEBA952E4283B54E88E6183CA', amf: '8000', sqn: NumberLong('64')},
    ambr: {downlink: {value: 1, unit: 3}, uplink: {value: 1, unit: 3}},
    slice: [{sst: 1, default_indicator: true, session: [{name: 'internet', type: 3,
      qos: {index: 9, arp: {priority_level: 8, pre_emption_capability: 1, pre_emption_vulnerability: 1}},
      ambr: {downlink: {value: 1, unit: 3}, uplink: {value: 1, unit: 3}}, pcc_rule: []}]}],
    access_restriction_data: 32, subscriber_status: 0, operator_determined_barring: 0,
    network_access_mode: 0, subscribed_rau_tau_timer: 12, __v: 0}}, {upsert: true});
}
print(db.subscribers.countDocuments());
