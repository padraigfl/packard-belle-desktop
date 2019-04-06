import React from "react";
import { Rnd } from "react-rnd";
import { SettingsContext } from "../../contexts/settings";
import "./_window.scss";

const resizeStyles = pixels => {
  const corners = pixels * 4;
  const halved = pixels / 2;
  return {
    bottom: { height: pixels, bottom: -pixels },
    bottomLeft: { height: corners, width: corners, left: -pixels },
    bottomRight: {
      height: corners,
      width: corners,
      right: -pixels * 2,
      bottom: -pixels * 2
    },
    left: { width: pixels, right: -pixels },
    right: { width: pixels, marginLeft: "100%" },
    top: { height: pixels },
    topLeft: { height: corners, width: corners, left: -pixels, top: -pixels },
    topRight: { width: 0, height: 0 }
  };
};

const getMaxes = document => {
  const holder = document.querySelector(".w98");

  if (holder && (holder.offsetWidth < 640 || holder.offsetHeight < 480)) {
    return {
      maxWidth: Math.ceil(holder.offsetWidth - 5),
      maxHeight: Math.ceil(holder.offsetHeight - 32)
    };
  }

  return {};
};

const randomizeLaunchSpot = max => Math.ceil(Math.random() * max);

const launchPositions = (propX, propY, isMobile) => {
  const random = randomizeLaunchSpot(80);
  const x = propX || random;
  const y = propY || random;
  return !isMobile
    ? {
        x,
        y
      }
    : {
        x: x / 2,
        y: y / 2
      };
};

class Window extends React.PureComponent {
  static contextType = SettingsContext;
  state = {
    height: this.props.initialHeight,
    width: this.props.initialWidth,
    maximized: this.context.isMobile && this.props.resizable,
    ...launchPositions(this.props.inintalX, this.props.initialY)
  };

  updateLocation = (a, b) =>
    this.setState({ x: b.x, y: b.y, isDragging: false });
  resize = (e, direction, ref, delta, position) =>
    this.setState({
      width: ref.style.width,
      height: ref.style.height,
      ...position
    });
  maximize = () => this.setState({ maximized: true });
  restore = () => this.setState({ maximized: false });
  toggleDrag = val => () => this.setState({ isDragging: val });
  toggleResize = val => () => this.setState({ isResizing: val });

  render() {
    const { context } = this;
    const resizeProps =
      this.props.resizable && !this.state.maximized
        ? {
            resizeHandleStyles: resizeStyles(4),
            onResize: this.resize,
            onResizeStart: this.toggleResize(true),
            onResizeStop: this.toggleResize(false)
          }
        : { resizeHandleStyles: resizeStyles(0) };

    const maximizedProps = this.state.maximized
      ? {
          size: { width: "100%" },
          position: { x: -2, y: -3 },
          disableDragging: true
        }
      : undefined;
    return (
      <>
        {this.state.isDragging && (
          <Rnd
            size={{ width: this.state.width, height: this.state.height }}
            position={{ x: this.state.x, y: this.state.y }}
            scale={context.scale}
          >
            {this.props.children({
              ...this,
              state: { ...this.state, isDragging: false }
            })}
          </Rnd>
        )}
        <Rnd
          className={this.state.maximized && "react-draggable-maximized-hack"}
          size={
            !this.state.maximized && {
              width: this.state.width,
              height: this.state.height
            }
          }
          position={{ x: this.state.x, y: this.state.y }}
          dragHandleClassName="Window__title"
          onDragStart={this.toggleDrag(true)}
          onDragStop={!this.state.maximized && this.updateLocation}
          bounds=".w98"
          minWidth={this.props.minWidth}
          minHeight={this.props.minHeight}
          maxWidth={!this.state.maximized ? this.props.maxWidth : "105%"}
          maxHeight={!this.state.maximized ? this.props.maxHeigh : "105%"}
          scale={context.scale}
          onMouseDown={
            this.props.moveToTop
              ? () => this.props.moveToTop(this.props)
              : undefined
          }
          {...resizeProps}
          {...maximizedProps}
          {...getMaxes(document)}
        >
          {this.props.children(this)}
        </Rnd>
      </>
    );
  }
}

Window.defaultProps = {
  minWidth: 160,
  minHeight: 160,
  // maxHeight: 448,
  // maxWidth: 635,
  resizable: true,

  scale: 1,
  title: "Needs default"
};

export default Window;
