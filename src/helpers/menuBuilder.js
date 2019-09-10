const buildCustomOptions = rows =>
  Object.keys(rows).reduce(
    (acc, val) => [
      ...acc,
      {
        title: val,
        options: rows[val]
      }
    ],
    []
  );

export const helpOptions = props => ({
  title: "Help",
  options: [
    [{ title: "Help Topics", isDisabled: true }],
    { title: `About ${props.title}`, isDisabled: true }
  ]
});

export const buildMenu = (props, customOptions = {}) => {
  const fileOptions = props.fileOptions || [];
  const onClose = [{ title: "Close", onClick: () => props.onClose(props) }];
  const saveOptions =
    props.onSave || props.onSaveAs
      ? [
          { title: "Save As...", onClick: data => props.onSaveAs(props, data) },
          {
            title: "Save",
            onClick: props.onSave && (data => props.onSave(props, data)),
            isDisabled: props.readOnly || !props.onSave
          }
        ]
      : [];
  const multiInstance = props.multiInstance
    ? [
        {
          title: "New",
          onClick: () => props.onOpen(props, { new: true }),
          isDisabled: props.singleInstance
        },
        {
          title: "Open...",
          isDisabled: !props.onOpenSearch,
          onClick: props.onOpenSearch
        }
      ]
    : [];
  if (props.multiWindow) {
    onClose.push([{ title: "Exit", onClick: () => props.onExit(props) }]);
  }
  const customElements = buildCustomOptions(customOptions);
  return [
    {
      title: "File",
      options: [...multiInstance, saveOptions, ...fileOptions, onClose]
    },
    ...customElements,
    helpOptions(props)
  ];
};

export default buildMenu;
